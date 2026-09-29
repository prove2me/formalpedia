-- Prove2me | solution 1 for NgoFL.resultant_weyl_invariant_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T17:45:42.416976+00:00
-- url     : https://prove2.me/submissions/217af679-cc3c-4858-b069-c4bd0bbdfd79

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

open NgoFL

namespace NgoFLRed

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  (P : RootPairing ι ℚ M N)

/-- The root indexed by `negIdx P i` is the negative of the root indexed by `i`. -/
lemma root_negIdx (i : ι) : P.root (negIdx P i) = - P.root i := by
  simp [negIdx]

lemma root'_negIdx (i : ι) (y : N) : P.root' (negIdx P i) y = - P.root' i y := by
  have : P.root (negIdx P i) = - P.root i := root_negIdx P i
  simp [RootPairing.root', this]

lemma negIdx_involutive (i : ι) : negIdx P (negIdx P i) = i := by
  apply P.root.injective
  rw [root_negIdx, root_negIdx, neg_neg]

lemma reflectionPerm_negIdx (j i : ι) :
    P.reflectionPerm j (negIdx P i) = negIdx P (P.reflectionPerm j i) := by
  apply P.root.injective
  rw [P.root_reflectionPerm, root_negIdx, root_negIdx, P.root_reflectionPerm, map_neg]

/-- Evaluating a root at a coreflected vector is evaluating the reflected root. -/
lemma root_reflectionPerm_eq (j i : ι) :
    P.root (P.reflectionPerm j i) = P.root i - P.pairing i j • P.root j := by
  rw [P.root_reflectionPerm]
  exact P.reflection_apply_root j i

lemma root'_coreflection (j i : ι) (y : N) :
    P.root' i (P.coreflection j y) = P.root' (P.reflectionPerm j i) y := by
  show P.toLinearMap (P.root i) (P.coreflection j y)
      = P.toLinearMap (P.root (P.reflectionPerm j i)) y
  rw [root_reflectionPerm_eq]
  simp [RootPairing.coreflection_apply, mul_comm]

variable [Fintype ι] [DecidableEq ι]

/-- A closed subsystem has a complement stable under its own reflections. -/
lemma compl_stable {s : Finset ι} (hs : IsClosedSubsystem P (s : Set ι)) {j : ι} (hj : j ∈ s)
    {i : ι} (hi : i ∈ sᶜ) : P.reflectionPerm j i ∈ sᶜ := by
  simp only [Finset.mem_compl] at hi ⊢
  intro hmem
  exact hi (by
    have := hs.reflectionPerm_mem j hj _ hmem
    simp [P.reflectionPerm_self] at this
    exact this)

variable [P.IsReduced]

/-- In a reduced system, no root outside a closed subsystem is negated by a reflection coming
from the subsystem. -/
lemma reflectionPerm_ne_negIdx {s : Finset ι} (hs : IsClosedSubsystem P (s : Set ι)) {j : ι}
    (hj : j ∈ s) {i : ι} (hi : i ∈ sᶜ) : P.reflectionPerm j i ≠ negIdx P i := by
  intro hEq
  have hroot : P.root i - P.pairing i j • P.root j = - P.root i := by
    rw [← root_reflectionPerm_eq, hEq, root_negIdx]
  have hdep : ¬ LinearIndependent ℚ ![P.root i, P.root j] := by
    intro hLin
    rw [LinearIndependent.pair_iff] at hLin
    obtain ⟨h4, -⟩ := hLin 2 (- P.pairing i j) (by
      rw [neg_smul, two_smul]
      linear_combination (norm := module) hroot)
    norm_num at h4
  have := RootPairing.IsReduced.eq_or_eq_neg (P := P) i j hdep
  have hmem : i ∈ s := by
    rcases this with h | h
    · have : i = j := P.root.injective h
      rwa [this]
    · have : i = negIdx P j := P.root.injective (by rw [h, root_negIdx])
      rw [this]
      exact hs.neg_mem j hj
  exact (Finset.mem_compl.1 hi) hmem

/-- The resultant is invariant under a single coreflection attached to the subsystem. -/
lemma resultant_coreflection {s L : Finset ι} (hs : IsClosedSubsystem P (s : Set ι))
    (hL : IsHalfSystem P sᶜ L) {j : ι} (hj : j ∈ s) (y : N) :
    resultant P L (P.coreflection j y) = resultant P L y := by
  classical
  set g : ι → ι := fun i => P.reflectionPerm j i with hg
  set psi : ι → ι := fun i => if g i ∈ L then g i else negIdx P (g i) with hpsi
  set e : ι → ℚ := fun i => if g i ∈ L then 1 else -1 with he
  -- `g` is an involution
  have hgg : ∀ i, g (g i) = i := fun i => P.reflectionPerm_self j i
  -- `g` commutes with negation of roots
  have hgn : ∀ i, g (negIdx P i) = negIdx P (g i) := fun i => reflectionPerm_negIdx P j i
  -- `g` preserves the complement of `s`
  have hgc : ∀ i ∈ sᶜ, g i ∈ sᶜ := fun i hi => compl_stable P hs hj hi
  -- membership of `L` in the complement
  have hLc : ∀ i ∈ L, i ∈ sᶜ := fun i hi => hL.subset hi
  -- the negation of an element of `L` is not in `L`
  have hnotL : ∀ i ∈ L, negIdx P i ∉ L := by
    intro i hi
    have hxor := hL.xor_mem i (hLc i hi)
    rcases hxor with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd hi h
  -- for an index of the complement outside `L`, its negative lies in `L`
  have hinL : ∀ i ∈ sᶜ, i ∉ L → negIdx P i ∈ L := by
    intro i hi hiL
    rcases hL.xor_mem i hi with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hiL
    · exact h
  -- `psi` maps `L` into `L`
  have hpsiL : ∀ i ∈ L, psi i ∈ L := by
    intro i hi
    by_cases h : g i ∈ L
    · simp [hpsi, h]
    · have : g i ∈ sᶜ := hgc i (hLc i hi)
      simpa [hpsi, h] using hinL _ this h
  -- `psi` is an involution of `L`
  have hpsipsi : ∀ i ∈ L, psi (psi i) = i := by
    intro i hi
    by_cases h : g i ∈ L
    · have h1 : psi i = g i := by simp [hpsi, h]
      have h2 : g (g i) = i := hgg i
      rw [h1]
      simp [hpsi, h2, hi]
    · have h1 : psi i = negIdx P (g i) := by simp [hpsi, h]
      have h2 : g (negIdx P (g i)) = negIdx P i := by rw [hgn, hgg]
      have h3 : negIdx P i ∉ L := hnotL i hi
      rw [h1]
      simp [hpsi, h2, h3, negIdx_involutive]
  -- the root evaluated along `g` factors through `psi` up to the sign `e`
  have hfac : ∀ i ∈ L, P.root' (g i) y = e i * P.root' (psi i) y := by
    intro i _
    by_cases h : g i ∈ L
    · simp [hpsi, he, h]
    · simp [hpsi, he, h, root'_negIdx]
  -- the signs cancel in pairs
  have hprod_e : ∏ i ∈ L, e i = 1 := by
    refine Finset.prod_involution (fun i _ => psi i) ?_ ?_ (fun i hi => hpsiL i hi)
      (fun i hi => hpsipsi i hi)
    · intro i hi
      by_cases h : g i ∈ L
      · have h1 : psi i = g i := by simp [hpsi, h]
        have h2 : g (psi i) = i := by rw [h1]; exact hgg i
        simp [he, h, h2, hi]
      · have h1 : psi i = negIdx P (g i) := by simp [hpsi, h]
        have h2 : g (psi i) = negIdx P i := by rw [h1, hgn, hgg]
        have h3 : negIdx P i ∉ L := hnotL i hi
        simp [he, h, h2, h3]
    · intro i hi _
      by_cases h : g i ∈ L
      · -- here `e i = 1`, so there is nothing to prove
        simp [he, h] at *
      · have h1 : psi i = negIdx P (g i) := by simp [hpsi, h]
        intro hEq
        rw [h1] at hEq
        have : g i = negIdx P i := by
          have := congrArg (negIdx P) hEq
          rwa [negIdx_involutive] at this
        exact reflectionPerm_ne_negIdx P hs hj (hLc i hi) this
  -- reindexing the product along the involution `psi`
  have hreindex : ∏ i ∈ L, P.root' (psi i) y = ∏ i ∈ L, P.root' i y := by
    refine Finset.prod_nbij' psi psi hpsiL hpsiL hpsipsi hpsipsi (fun a _ => rfl)
  calc resultant P L (P.coreflection j y)
      = ∏ i ∈ L, P.root' (g i) y := by
        refine Finset.prod_congr rfl fun i _ => ?_
        exact root'_coreflection P j i y
    _ = ∏ i ∈ L, (e i * P.root' (psi i) y) := Finset.prod_congr rfl hfac
    _ = (∏ i ∈ L, e i) * ∏ i ∈ L, P.root' (psi i) y := Finset.prod_mul_distrib
    _ = ∏ i ∈ L, P.root' i y := by rw [hprod_e, hreindex, one_mul]
    _ = resultant P L y := rfl

end NgoFLRed

/-- **Ngô, Lemme 1.10.2** for a reduced root system: the resultant
`R^G_H = ∏_{α ∈ Λ} dα` is invariant under the Weyl group `W_H` of the endoscopic subsystem. -/
theorem solution {ι M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [Fintype ι] [DecidableEq ι] (P : RootPairing ι ℚ M N)
    [P.IsRootSystem] [P.IsReduced] (s L : Finset ι) (hs : IsClosedSubsystem P (s : Set ι))
    (hL : IsHalfSystem P sᶜ L) (w : N ≃ₗ[ℚ] N)
    (hw : w ∈ weylSubgroup P (s : Set ι)) (x : N) :
    resultant P L (w x) = resultant P L x := by
  classical
  have hsub : weylSubgroup P (s : Set ι) ≤
      { carrier := {f : N ≃ₗ[ℚ] N | ∀ y, resultant P L (f y) = resultant P L y}
        one_mem' := fun y => rfl
        mul_mem' := by
          intro a b ha hb y
          simp only [Set.mem_ofPred_eq] at ha hb
          rw [LinearEquiv.mul_apply, ha, hb]
        inv_mem' := by
          intro a ha y
          simp only [Set.mem_ofPred_eq] at ha ⊢
          have h := ha (a⁻¹ y)
          rw [show a (a⁻¹ y) = y from by simp] at h
          exact h.symm } := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro f ⟨i, hi, rfl⟩ y
    exact NgoFLRed.resultant_coreflection P hs hL (by simpa using hi) y
  exact hsub hw x
