-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:17:39.363282+00:00
-- url     : https://prove2.me/submissions/6254b83d-29d0-4029-8898-f0ed42b392c7

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Best
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

lemma best_spec (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V) :
    best F hF shape X ∈ F ∧
      ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape (best F hF shape X)).card :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma chosen_mem (k : ℕ) : chosen F hF shape X k ∈ F :=
  (best_spec F hF shape _).1

lemma maximal_cell (k : ℕ) (a : I) (ha : a ∈ F) :
    (remaining F hF shape X k ∩ shape a).card ≤ (cell F hF shape X k).card :=
  (best_spec F hF shape _).2 a ha

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma cell_card_antitone : Antitone (fun k => (cell F hF shape X k).card) := by
  apply antitone_nat_of_succ_le
  intro k
  have hle : remaining F hF shape X (k+1) ∩ shape (chosen F hF shape X (k+1)) ⊆
      remaining F hF shape X k ∩ shape (chosen F hF shape X (k+1)) :=
    Finset.inter_subset_inter_right (remaining_succ_subset F hF shape X k)
  exact (Finset.card_le_card hle).trans (maximal_cell F hF shape X k _ (chosen_mem F hF shape X _))

lemma remaining_eq_sdiff_union (k : ℕ) :
    remaining F hF shape X k = X \ (Finset.range k).biUnion (fun j => shape (chosen F hF shape X j)) := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    change remaining F hF shape X k \ shape (chosen F hF shape X k) = _
    rw [ih]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
    change (x ∈ X ∧ ¬∃ j < k, x ∈ shape (chosen F hF shape X j)) ∧
        x ∉ shape (chosen F hF shape X k) ↔
      x ∈ X ∧ ¬∃ j < k+1, x ∈ shape (chosen F hF shape X j)
    constructor
    · rintro ⟨⟨hx,hn⟩,hk⟩
      refine ⟨hx,?_⟩
      rintro ⟨j,hj,hxj⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hj | rfl
      · exact hn ⟨j,hj,hxj⟩
      · exact hk hxj
    · rintro ⟨hx,hn⟩
      refine ⟨⟨hx,?_⟩,?_⟩
      · rintro ⟨j,hj,hxj⟩
        exact hn ⟨j,Nat.lt_succ_of_lt hj,hxj⟩
      · intro hxk
        exact hn ⟨k,Nat.lt_succ_self k,hxk⟩

lemma firstAt_mem (J : ℕ) (x : V) (h : firstAt F hF shape X J x < J) :
    x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) := by
  have hs := Nat.find_spec (show ∃ j, J ≤ j ∨ x ∈ shape (chosen F hF shape X j) from ⟨J,Or.inl le_rfl⟩)
  change J ≤ firstAt F hF shape X J x ∨ x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) at hs
  exact hs.resolve_left (not_le_of_gt h)

lemma firstAt_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    firstAt F hF shape X J x = j := by
  apply le_antisymm
  · exact Nat.find_min' _ (Or.inr hxj)
  · by_contra hn
    have hlt : firstAt F hF shape X J x < j := by omega
    exact hearlier _ hlt (firstAt_mem F hF shape X J x (hlt.trans hj))

lemma ownCell_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    ownCell F hF shape X J x = cell F hF shape X j := by
  rw [ownCell, firstAt_eq F hF shape X J j x hj hxj hearlier, ite_eq_left hj]

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndexMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyWeightedCount
open scoped BigOperators

lemma index_mul_le {J j : ℕ} (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hmono : Antitone s) (hj : j < J) :
    (j:ℝ)*s j ≤ ∑ i ∈ Finset.range J, s i := by
  have hsum : ∑ i ∈ Finset.range j, s j ≤ ∑ i ∈ Finset.range j, s i :=
    Finset.sum_le_sum (fun i hi => hmono (Finset.mem_range.mp hi).le)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj.le)
    (fun i _ _ => hs i))

theorem weighted_rich_count (J : ℕ) (s m : ℕ → ℝ) (q M n p N : ℝ)
    (hs : ∀ i, 0 ≤ s i) (hmono : Antitone s)
    (hm : ∀ i < J, 0 ≤ m i ∧ m i ≤ N)
    (hq : 0 ≤ q) (hM : 0 < M) (hp : 0 ≤ p) (hN : 0 ≤ N)
    (hpn : p*q ≤ 1) (hNq : N ≤ 3*q^2)
    (hbudget : ∑ i ∈ Finset.range J, s i ≤ n) (hJq : (J:ℝ)*q ≤ n)
    (hvariance : ∀ i < J, 2*p*s i ≤ M → m i*M^2 ≤ 4*q*s i) :
    (∑ i ∈ Finset.range J, (i:ℝ)*m i)*M^2 ≤ 12*n^2 := by
  have hn : 0 ≤ n := (mul_nonneg (Nat.cast_nonneg _) hq).trans hJq
  have hNp : N*p^2 ≤ 3 := by
    have hpq : (p*q)^2 ≤ 1 := by nlinarith [mul_nonneg hp hq]
    have hh := mul_le_mul_of_nonneg_right hNq (sq_nonneg p)
    nlinarith
  have hrow (i : ℕ) (hi : i ∈ Finset.range J) : (i:ℝ)*m i*M^2 ≤ 12*n*s i := by
    have hiJ := Finset.mem_range.mp hi
    have hiq : (i:ℝ)*q ≤ n :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hiJ.le) hq).trans hJq
    have his : (i:ℝ)*s i ≤ n := (index_mul_le s hs hmono hiJ).trans hbudget
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have hsi := hs i
    rcases hm i hiJ with ⟨hm0,hmN⟩
    by_cases hsmall : 2*p*s i ≤ M
    · have hh := mul_le_mul_of_nonneg_left (hvariance i hiJ hsmall) hi0
      have hq' := mul_le_mul_of_nonneg_right hiq (hs i)
      have hn' := mul_nonneg hn (hs i)
      nlinarith
    · have hsquare : M^2 ≤ 4*p^2*(s i)^2 := by
        have hh : M ≤ 2*p*s i := (lt_of_not_ge hsmall).le
        have hsq := pow_le_pow_left₀ hM.le hh 2
        nlinarith
      calc
        (i:ℝ)*m i*M^2 ≤ (i:ℝ)*N*(4*p^2*(s i)^2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hmN hi0) hsquare
            (sq_nonneg M) (mul_nonneg hi0 hN)
        _ = 4*(N*p^2)*((i:ℝ)*s i)*s i := by ring
        _ ≤ 4*3*n*s i := by gcongr
        _ = 12*n*s i := by ring
  rw [Finset.sum_mul]
  calc
    ∑ i ∈ Finset.range J, (i:ℝ)*m i*M^2 ≤ ∑ i ∈ Finset.range J, 12*n*s i :=
      Finset.sum_le_sum hrow
    _ = 12*n*(∑ i ∈ Finset.range J, s i) := by rw [Finset.mul_sum]
    _ ≤ 12*n*n := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = 12*n^2 := by ring
end SharpRamseyFive.GreedyWeightedCount

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace RadialLine

lemma through_eq_iff [FiniteDimensional K V] {x y : ℙ K V} (hxy : x ≠ y)
    (l : RadialLine x) : through x y hxy = l ↔ y.submodule ≤ l.val := by
  constructor
  · intro h
    rw [← h]
    exact le_sup_right
  · intro h
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq (sup_le l.property.2 h)
      ((finrank_sup_points hxy).trans l.property.1.symm)

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ExceptionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma ker_dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) :
    LinearMap.ker (dualOfHyperplane hdim A hA).rep = A := by
  let b := dualOfHyperplane hdim A hA
  have he : b.submodule = A.dualAnnihilator := Projectivization.submodule_mk'' _ _
  have hmem : b.rep ∈ A.dualAnnihilator := by
    rw [← he, b.submodule_eq]
    exact Submodule.mem_span_singleton_self _
  have hle : A ≤ LinearMap.ker b.rep := by
    intro a ha
    exact ((Submodule.mem_dualAnnihilator b.rep).mp hmem) a ha
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hA]; omega)).symm

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RichHyperplaneVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem rich_hyperplane_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (X : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V))) (M : ℕ)
    (hM : ∀ b ∈ B, M ≤ (X.filter fun x => Incident x b).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (B.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K V) := Fintype.ofFinite _
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let w (x : ℙ K V) : ℝ := if x ∈ X then 1 else 0
  have hw : ∑ x, w x = (X.card:ℝ) := by simp [w]
  have hw2 : ∑ x, w x^2 = (X.card:ℝ) := by simp [w]
  have hweight (b : ℙ K (Module.Dual K V)) :
      weightOnHyperplane w b = ((X.filter fun x => Incident x b).card:ℝ) := by
    simp [weightOnHyperplane, incidenceEntry, w, mul_ite]
  let μ : ℝ := ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card
  have hvariance := incidence_variance hdim hd w
  rw [hw,hw2] at hvariance
  have hrow (b : ℙ K (Module.Dual K V)) (hb : b ∈ B) :
      (M:ℝ)^2 ≤ 4*(weightOnHyperplane w b-μ)^2 := by
    have hm : (M:ℝ) ≤ weightOnHyperplane w b := by rw [hweight]; exact_mod_cast hM b hb
    have hmean' : 2*μ ≤ M := by dsimp [μ]; nlinarith [hmean]
    have hm0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hle : 0 ≤ 2*(weightOnHyperplane w b-μ)-(M:ℝ) := by linarith
    have hge : 0 ≤ 2*(weightOnHyperplane w b-μ)+(M:ℝ) := by linarith
    nlinarith [mul_nonneg hle hge]
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
  have hsub := Finset.sum_le_univ_sum_of_nonneg (s := B)
    (fun b => sq_nonneg (weightOnHyperplane w b-μ))
  have hvar : ∑ b, (weightOnHyperplane w b-μ)^2 ≤ (Nat.card K:ℝ)^(d-1)*X.card := hvariance
  linarith

theorem rich_subspaces_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*X.card ≤ M) :
    (F.card:ℝ)*M^2 ≤ 4*(Nat.card K:ℝ)^(d-1)*X.card := by
  let b (A : F) : ℙ K (Module.Dual K V) := dualOfHyperplane hdim A.val (hF A.val A.property)
  let B := F.attach.image b
  have hi : Function.Injective b := by
    intro A B hAB
    apply Subtype.ext
    have h := congrArg (fun c : ℙ K (Module.Dual K V) => LinearMap.ker c.rep) hAB
    simpa only [b,ker_dualOfHyperplane] using h
  have hBc : B.card = F.card := by simp [B,Finset.card_image_of_injective _ hi]
  have hrich (c : ℙ K (Module.Dual K V)) (hc : c ∈ B) :
      M ≤ (X.filter fun x => Incident x c).card := by
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hc
    simpa only [Incident,b,ker_dualOfHyperplane] using hM A.val A.property
  have h := rich_hyperplane_variance hdim hd X B M hrich hmean
  simpa only [hBc] using h

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma card_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) :
    (pointsInSubspace H X).card = (X.filter fun p => p.submodule ≤ H).card := by
  simp [pointsInSubspace]

lemma mem_pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) (p : ℙ K H) :
    p ∈ pointsInSubspace H X ↔ ((subspacePointsEquiv H) p).val ∈ X := by
  simp [pointsInSubspace]

lemma subspacePointsEquiv_submodule (H A : Submodule K V) (p : ℙ K H) :
    p.submodule ≤ A.comap H.subtype ↔ ((subspacePointsEquiv H) p).val.submodule ≤ A := by
  induction p using Projectivization.ind with | h v hv =>
  change (Projectivization.mk K v hv).submodule ≤ A.comap H.subtype ↔
    (Projectivization.map H.subtype H.injective_subtype (Projectivization.mk K v hv)).submodule ≤ A
  rw [Projectivization.map_mk, Projectivization.submodule_mk,
    Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem,
    Submodule.span_singleton_le_iff_mem]
  rfl

lemma card_pointsInSubspace_filter (H A : Submodule K V) (hAH : A ≤ H)
    (X : Finset (ℙ K V)) :
    ((pointsInSubspace H X).filter fun p => p.submodule ≤ A.comap H.subtype).card =
      (X.filter fun p => p.submodule ≤ A).card := by
  apply Finset.card_bij (fun p _ => ((subspacePointsEquiv H) p).val)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(mem_pointsInSubspace H X p).mp hpX,
      (subspacePointsEquiv_submodule H A p).mp hpA⟩
  · intro p hp q hq hpq
    exact (subspacePointsEquiv H).injective (Subtype.ext hpq)
  · intro p hp
    obtain ⟨hpX,hpA⟩ := Finset.mem_filter.mp hp
    let z : {p : ℙ K V // p.submodule ≤ H} := ⟨p,hpA.trans hAH⟩
    refine ⟨(subspacePointsEquiv H).symm z, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · rw [mem_pointsInSubspace, Equiv.apply_symm_apply]
        exact hpX
      · rw [subspacePointsEquiv_submodule, Equiv.apply_symm_apply]
        exact hpA
    · simp [z]

lemma comap_subtype_finrank [FiniteDimensional K V] (H A : Submodule K V) (hAH : A ≤ H) :
    finrank K (A.comap H.subtype) = finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq H, Submodule.map_comap_subtype, inf_eq_right.mpr hAH]

lemma comap_subtype_injOn (H : Submodule K V) :
    Set.InjOn (fun A : Submodule K V => A.comap H.subtype) {A | A ≤ H} := by
  intro A hA B hB hAB
  change A ≤ H at hA
  change B ≤ H at hB
  have he := congrArg (fun W : Submodule K H => W.map H.subtype) hAB
  simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr hA, inf_eq_right.mpr hB] using he

theorem rich_hyperplanes_inside_subspace [FiniteDimensional K V] [Finite K]
    {d : ℕ} (hd : 1 ≤ d) (H : Submodule K V) (hH : finrank K H = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d)
    (X : Finset (ℙ K V)) (M : ℕ)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hmean : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*
      (X.filter fun p => p.submodule ≤ H).card ≤ M) :
    ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)^(d-1)*(X.filter fun p => p.submodule ≤ H).card := by
  let G := F.filter fun A => A ≤ H
  let FH := G.image (fun A => A.comap H.subtype)
  have hc : FH.card = G.card := Finset.card_image_iff.mpr (by
    intro A hA B hB he
    exact comap_subtype_injOn H (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 he)
  have hdimF (A : Submodule K H) (hA : A ∈ FH) : finrank K A = d := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [comap_subtype_finrank H B (Finset.mem_filter.mp hB).2]
    exact hF B (Finset.mem_filter.mp hB).1
  have hm (A : Submodule K H) (hA : A ∈ FH) :
      M ≤ ((pointsInSubspace H X).filter fun p => p.submodule ≤ A).card := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [card_pointsInSubspace_filter H B (Finset.mem_filter.mp hB).2]
    exact hM B (Finset.mem_filter.mp hB).1
  have hμ : 2*((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(pointsInSubspace H X).card ≤ M := by
    simpa only [card_pointsInSubspace] using hmean
  have hh := rich_subspaces_variance hH hd FH hdimF (pointsInSubspace H X) M hm hμ
  simpa only [hc, card_pointsInSubspace] using hh

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CardFilterContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma card_filter_containment_le (X : Finset (ℙ K V)) (A : Submodule K V) :
    (X.filter fun x => x.submodule ≤ A).card ≤ ∑ i ∈ Finset.range (finrank K A), Nat.card K^i := by
  let : Finite V := Module.finite_of_finite K
  let Y := X.filter fun x => x.submodule ≤ A
  have hi : Function.Injective (fun x : Y => (⟨x.val,(Finset.mem_filter.mp x.property).2⟩ :
      {p : ℙ K V // p.submodule ≤ A})) := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : {p : ℙ K V // p.submodule ≤ A} => z.val) he)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_subspacePoints] at hc
  exact hc

lemma card_filter_finrank_le_one (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A ≤ 1) :
    (X.filter fun x => x.submodule ≤ A).card ≤ 1 := by
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hA)
    (f := fun i => Nat.card K^i) (by intros; exact Nat.zero_le _)
  have hc := (card_filter_containment_le X A).trans hle
  simpa using hc

omit [Finite K] in
lemma finrank_inf_lt_of_not_le (A H : Submodule K V) (hn : ¬A ≤ H) :
    finrank K (A ⊓ H : Submodule K V) < finrank K A := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro he
  exact hn (he ▸ inf_le_right)

lemma line_noncontaining_flat_cap (X : Finset (ℙ K V)) (A H : Submodule K V)
    (hA : finrank K A = 2) (hn : ¬A ≤ H) :
    (X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ H).card ≤ 1 := by
  have hh := finrank_inf_lt_of_not_le A H hn
  rw [hA] at hh
  simpa only [le_inf_iff] using card_filter_finrank_le_one X (A ⊓ H) (by omega)

lemma card_hyperplane_family {d : ℕ} (hdim : finrank K V = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) :
    F.card ≤ Q (Nat.card K) d := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let : Fintype (ℙ K (Module.Dual K V)) := Fintype.ofFinite _
  let f (A : F) := dualOfHyperplane hdim A.val (hF A.val A.property)
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hk := congrArg (fun b : ℙ K (Module.Dual K V) => LinearMap.ker b.rep) he
    simpa only [f,ker_dualOfHyperplane] using hk
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, card_hyperplanes hdim] using hc

lemma card_hyperplanes_inside {d : ℕ} (H : Submodule K V) (hH : finrank K H = d+1)
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = d) :
    (F.filter fun A => A ≤ H).card ≤ Q (Nat.card K) d := by
  let G := F.filter fun A => A ≤ H
  let FH := G.image (fun A => A.comap H.subtype)
  have hc : FH.card = G.card := Finset.card_image_iff.mpr (by
    intro A hA B hB he
    exact comap_subtype_injOn H (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 he)
  have hdimF (A : Submodule K H) (hA : A ∈ FH) : finrank K A = d := by
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    rw [comap_subtype_finrank H B (Finset.mem_filter.mp hB).2]
    exact hF B (Finset.mem_filter.mp hB).1
  have hh := card_hyperplane_family hH FH hdimF
  rwa [hc] at hh

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma mem_flatPoints (A : Submodule K V) (x : ℙ K V) :
    x ∈ flatPoints A ↔ x.submodule ≤ A := by
  simp [flatPoints]

lemma line_covered_cap {I : Type*} [DecidableEq I] (T : Finset I)
    (P : I → Submodule K V) (X : Finset (ℙ K V)) (A : Submodule K V)
    (hA : finrank K A = 2) (hn : ∀ i ∈ T, ¬A ≤ P i)
    (hcover : ∀ x ∈ X, x.submodule ≤ A → ∃ i ∈ T, x.submodule ≤ P i) :
    (X.filter fun x => x.submodule ≤ A).card ≤ T.card := by
  let Y (i : I) := X.filter fun x => x.submodule ≤ A ∧ x.submodule ≤ P i
  have hsub : X.filter (fun x => x.submodule ≤ A) ⊆ T.biUnion Y := by
    intro x hx
    obtain ⟨hxX,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨i,hi,hxi⟩ := hcover x hxX hxA
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hxX,hxA,hxi⟩⟩
  have hsum : ∑ i ∈ T, (Y i).card ≤ ∑ _i ∈ T, (1:ℕ) :=
    Finset.sum_le_sum (fun i hi => line_noncontaining_flat_cap X A (P i) hA (hn i hi))
  exact (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans (by simpa using hsum))

variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma captured_cover (J : ℕ) (x : ℙ K V)
    (hx : x ∈ X \ remaining F hF (fun i => flatPoints (P i)) X J) :
    ∃ j ∈ Finset.range J, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  rw [remaining_eq_sdiff_union] at hx
  have hxnot := (Finset.mem_sdiff.mp hx).2
  have hxX := (Finset.mem_sdiff.mp hx).1
  have hm : x ∈ (Finset.range J).biUnion (fun j => flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X j))) := by
    by_contra hn
    exact hxnot (Finset.mem_sdiff.mpr ⟨hxX,hn⟩)
  obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hm
  exact ⟨j,hj,(mem_flatPoints _ _).mp hxj⟩

lemma rich_line_has_containing_flat (J M : ℕ) (hJM : J < M)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hM : M ≤ ((X \ remaining F hF (fun i => flatPoints (P i)) X J).filter
      fun x => x.submodule ≤ A).card) :
    ∃ j < J, A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := by
  by_contra hn
  push Not at hn
  have hc := line_covered_cap (Finset.range J)
    (fun j => P (chosen F hF (fun i => flatPoints (P i)) X j))
    (X \ remaining F hF (fun i => flatPoints (P i)) X J) A hA
    (fun j hj => hn j (Finset.mem_range.mp hj))
    (fun x hx _ => captured_cover F hF P X J x hx)
  rw [Finset.card_range] at hc
  omega

lemma outside_cell_earlier (j : ℕ) (A : Submodule K V)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (y : ℙ K V) (hyX : y ∈ X) (hyA : y.submodule ≤ A)
    (hycell : y ∉ cell F hF (fun i => flatPoints (P i)) X j) :
    y ∈ X \ remaining F hF (fun i => flatPoints (P i)) X j := by
  refine Finset.mem_sdiff.mpr ⟨hyX, ?_⟩
  intro hyr
  exact hycell (Finset.mem_inter.mpr ⟨hyr, (mem_flatPoints _ _).mpr (hyA.trans hAj)⟩)

lemma earliest_line_outside_cell_cap (j : ℕ) (A : Submodule K V)
    (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      fun y => y.submodule ≤ A).card ≤ j := by
  have hs : (X \ cell F hF (fun i => flatPoints (P i)) X j).filter
      (fun y => y.submodule ≤ A) ⊆
      (X \ remaining F hF (fun i => flatPoints (P i)) X j).filter
        (fun y => y.submodule ≤ A) := by
    intro y hy
    obtain ⟨hy,hya⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyX,hyc⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_filter.mpr ⟨outside_cell_earlier F hF P X j A hAj y hyX hya hyc,hya⟩
  have hc := line_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i))
    (X \ remaining F hF (fun i => flatPoints (P i)) X j) A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi))
    (fun y hy _ => captured_cover F hF P X j y hy)
  exact (Finset.card_le_card hs).trans (by simpa only [Finset.card_range] using hc)

lemma surviving_line_center_earlier (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (x : ℙ K V) (hxA : x.submodule ≤ A)
    (hrich : j < ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card) :
    ∃ i < j, x.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
  by_contra hn
  push Not at hn
  have heq := ownCell_eq F hF (fun i => flatPoints (P i)) X J j x hj
    ((mem_flatPoints _ _).mpr (hxA.trans hAj))
    (fun i hi hmem => hn i hi ((mem_flatPoints _ _).mp hmem))
  rw [heq] at hrich
  exact (not_lt_of_ge (earliest_line_outside_cell_cap F hF P X j A hA hAj hearlier)) hrich

lemma surviving_line_centers_cap (J j : ℕ) (hj : j < J)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i)) :
    ((flatPoints A).filter fun x => j <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card).card ≤ j := by
  let C := (flatPoints A).filter fun x => j <
      ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter
      fun y => y.submodule ≤ A).card
  have hall (x : ℙ K V) (hx : x ∈ C) : x.submodule ≤ A :=
    (mem_flatPoints _ _).mp (Finset.mem_filter.mp hx).1
  have hc := line_covered_cap (Finset.range j)
    (fun i => P (chosen F hF (fun i => flatPoints (P i)) X i)) C A hA
    (fun i hi => hearlier i (Finset.mem_range.mp hi)) (by
      intro x hx hxa
      obtain ⟨i,hi,hxi⟩ := surviving_line_center_earlier F hF P X J j hj A hA hAj hearlier
        x hxa (Finset.mem_filter.mp hx).2
      exact ⟨i,Finset.mem_range.mpr hi,hxi⟩)
  rw [Finset.filter_eq_self.mpr hall,Finset.card_range] at hc
  exact hc

lemma cell_filter_own_flat (j : ℕ) :
    ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y =>
      y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cell F hF (fun i => flatPoints (P i)) X j := by
  apply Finset.filter_eq_self.mpr
  intro y hy
  exact (mem_flatPoints _ _).mp (Finset.mem_inter.mp hy).2

lemma card_cellRichLines_le (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (j M : ℕ) :
    (cellRichLines F hF P X L j M).card ≤ ProjectiveIncidence.Q (Nat.card K) 2 := by
  apply (Finset.card_le_card (show cellRichLines F hF P X L j M ⊆
      L.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) from
      fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,(Finset.mem_filter.mp hA).2.1⟩)).trans
  exact card_hyperplanes_inside _ (hP _ (chosen_mem F hF _ X j)) L hL

lemma cellRichLines_variance (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (j M : ℕ)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 1:ℝ)/ProjectiveIncidence.Q (Nat.card K) 2)*
      (cell F hF (fun i => flatPoints (P i)) X j).card ≤ M) :
    ((cellRichLines F hF P X L j M).card:ℝ)*M^2 ≤
      4*(Nat.card K:ℝ)*(cell F hF (fun i => flatPoints (P i)) X j).card := by
  let C := cell F hF (fun i => flatPoints (P i)) X j
  let G := L.filter fun A => M ≤ (C.filter fun y => y.submodule ≤ A).card
  have hG (A : Submodule K V) (hA : A ∈ G) : finrank K A = 2 :=
    hL A (Finset.mem_filter.mp hA).1
  have hm (A : Submodule K V) (hA : A ∈ G) : M ≤ (C.filter fun y => y.submodule ≤ A).card :=
    (Finset.mem_filter.mp hA).2
  have hμ : 2*((ProjectiveIncidence.Q (Nat.card K) (2-1):ℝ)/ProjectiveIncidence.Q (Nat.card K) 2)*
      (C.filter fun y => y.submodule ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)).card ≤ M := by
    simpa only [C,cell_filter_own_flat] using hmean
  have hh := rich_hyperplanes_inside_subspace (by omega : 1 ≤ (2:ℕ))
    (P (chosen F hF (fun i => flatPoints (P i)) X j)) (hP _ (chosen_mem F hF _ X j))
    G hG C M hm hμ
  have he : G.filter (fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) =
      cellRichLines F hF P X L j M := by
    ext A
    simp only [G,cellRichLines,Finset.mem_filter,C]
    tauto
  simpa only [he,C,cell_filter_own_flat,show (2:ℕ)-1=1 from rfl,pow_one] using hh

theorem weighted_cell_rich_lines (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (J M : ℕ)
    (hM : 0 < M) (hJ : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card) :
    (∑ j ∈ Finset.range J, (j:ℝ)*(cellRichLines F hF P X L j M).card)*(M:ℝ)^2 ≤
      12*(X.card:ℝ)^2 := by
  let q : ℝ := Nat.card K
  let N : ℝ := ProjectiveIncidence.Q (Nat.card K) 2
  let p : ℝ := (ProjectiveIncidence.Q (Nat.card K) 1:ℝ)/N
  let s (j : ℕ) : ℝ := (cell F hF (fun i => flatPoints (P i)) X j).card
  let m (j : ℕ) : ℝ := (cellRichLines F hF P X L j M).card
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (show 1 ≤ Nat.card K from (Finite.one_lt_card (α := K)).le)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 2
  have hpq : p*q ≤ 1 := by
    dsimp [p,q,N]
    rw [div_mul_eq_mul_div]
    apply (div_le_one (by exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 2)).mpr
    have he := ProjectiveIncidence.Q_recurrence (q := Nat.card K) (d := 2) (by omega)
    push_cast [he]
    nlinarith
  have hNq : N ≤ 3*q^2 := by
    have he : N = 1+q+q^2 := by
      simp [N,q,ProjectiveIncidence.Q,Finset.sum_range_succ]
    rw [he]
    nlinarith
  have hbudget : ∑ j ∈ Finset.range J, s j ≤ X.card := by
    have hh := sum_card_add_remaining F hF (fun i => flatPoints (P i)) X J
    have hn : ∑ j ∈ Finset.range J, (cell F hF (fun i => flatPoints (P i)) X j).card ≤ X.card := by omega
    dsimp [s]
    exact_mod_cast hn
  apply GreedyWeightedCount.weighted_rich_count J s m q M X.card p N
  · intro j; exact Nat.cast_nonneg _
  · intro i j hij
    dsimp [s]
    exact_mod_cast cell_card_antitone F hF (fun i => flatPoints (P i)) X hij
  · intro j _
    exact ⟨Nat.cast_nonneg _, by dsimp [m,N]; exact_mod_cast card_cellRichLines_le F hF P X hP L hL j M⟩
  · exact hq.trans' zero_le_one
  · exact_mod_cast hM
  · dsimp [p]; positivity
  · exact hN.le
  · exact hpq
  · exact hNq
  · exact hbudget
  · exact hJ
  · intro j _ hj
    exact cellRichLines_variance F hF P X hP L hL j M hj

lemma earliest_line_cell_rich (j M : ℕ) (hj : j ≤ M)
    (A : Submodule K V) (hA : finrank K A = 2)
    (hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j))
    (hearlier : ∀ i < j, ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i))
    (hrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card) :
    M ≤ ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A).card := by
  have hcap := earliest_line_outside_cell_cap F hF P X j A hA hAj hearlier
  have hsub : X.filter (fun y => y.submodule ≤ A) ⊆
      ((X \ cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) ∪
      ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A) := by
    intro y hy
    simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_sdiff] at *
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem captured_center_line_count (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2) (J M : ℕ)
    (hM : 0 < M) (hJM : J ≤ M) (hJq : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card) :
    (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(M:ℝ)^2 ≤
      12*(X.card:ℝ)^2 := by
  have hrow (A : Submodule K V) (hA : A ∈ L) :
      ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) ≤
        ∑ j ∈ Finset.range J, if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0 := by
    by_cases he : (capturedLineCenters F hF P X J (2*M) A).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxc := (Finset.mem_filter.mp hx).2
      have hcaprich : 2*M ≤ ((X \ remaining F hF (fun i => flatPoints (P i)) X J).filter
          fun y => y.submodule ≤ A).card :=
        hxc.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hfullrich : 2*M ≤ (X.filter fun y => y.submodule ≤ A).card :=
        hcaprich.trans (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset))
      have hcont := rich_line_has_containing_flat F hF P X J (2*M) (by omega) A (hL A hA) hcaprich
      let j := Nat.find hcont
      have hj : j < J := (Nat.find_spec hcont).1
      have hAj : A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) := (Nat.find_spec hcont).2
      have hearlier (i : ℕ) (hi : i < j) : ¬A ≤ P (chosen F hF (fun i => flatPoints (P i)) X i) := by
        intro hiA
        exact Nat.find_min hcont hi ⟨hi.trans hj,hiA⟩
      have hmem : A ∈ cellRichLines F hF P X L j M :=
        Finset.mem_filter.mpr ⟨hA,hAj,earliest_line_cell_rich F hF P X j M
          (hj.le.trans hJM) A (hL A hA) hAj hearlier hfullrich⟩
      have hsub : capturedLineCenters F hF P X J (2*M) A ⊆
          (flatPoints A).filter (fun z => j <
            ((X \ ownCell F hF (fun i => flatPoints (P i)) X J z).filter fun y => y.submodule ≤ A).card) := by
        intro z hz
        obtain ⟨hzA,hzr⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_filter.mpr ⟨hzA, ?_⟩
        have hc := hzr.trans (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.sdiff_subset_sdiff_left _ Finset.sdiff_subset)))
        omega
      have hc := (Finset.card_le_card hsub).trans
        (surviving_line_centers_cap F hF P X J j hj A (hL A hA) hAj hearlier)
      have hsingle : (j:ℝ) ≤ ∑ k ∈ Finset.range J,
          if A ∈ cellRichLines F hF P X L k M then (k:ℝ) else 0 := by
        have hh := Finset.single_le_sum (s := Finset.range J)
          (f := fun k => if A ∈ cellRichLines F hF P X L k M then (k:ℝ) else 0)
          (fun k _ => by positivity) (Finset.mem_range.mpr hj)
        simpa only [ite_eq_left hmem] using hh
      exact (by exact_mod_cast hc : ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) ≤ (j:ℝ)).trans hsingle
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.cast_zero]
      exact Finset.sum_nonneg (fun j _ => by positivity)
  have hsum := Finset.sum_le_sum hrow
  have hcount (j : ℕ) :
      (∑ A ∈ L, if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0) =
        (j:ℝ)*(cellRichLines F hF P X L j M).card := by
    have hsub : cellRichLines F hF P X L j M ⊆ L := Finset.filter_subset _ _
    have hh := Finset.sum_subset hsub (f := fun A => if A ∈ cellRichLines F hF P X L j M then (j:ℝ) else 0)
      (fun _ _ hn => ite_eq_right hn)
    rw [← hh]
    simp [mul_comm]
  rw [Finset.sum_comm] at hsum
  simp_rw [hcount] at hsum
  exact (mul_le_mul_of_nonneg_right hsum (sq_nonneg _)).trans
    (weighted_cell_rich_lines F hF P X hP L hL J M hM hJq)

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_RichCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma richCenters_mono (S T : Finset (ℙ K V))
    (O U : ℙ K V → Finset (ℙ K V)) (δ a : ℝ) (hδ : 0 ≤ δ)
    (hS : S ⊆ T) (hO : ∀ x, U x ⊆ O x) (A : Submodule K V) :
    richCenters S O δ a A ⊆ richCenters T U δ a A := by
  intro x hx
  obtain ⟨hxA,hx⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxA,hx.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hδ
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.sdiff_subset_sdiff hS (Finset.union_subset_union_left (hO x))))

lemma exists_scale {δ a : ℝ} (hδ : 0 < δ) (ha : 4*δ ≤ a) :
    ∃ M : ℕ, 0 < M ∧ 2*δ*M ≤ a ∧ a ≤ 4*δ*M := by
  have hx : 2 ≤ a/(2*δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hp : 1 ≤ ⌊a/(2*δ)⌋₊ := Nat.le_floor (by linarith)
  refine ⟨⌊a/(2*δ)⌋₊,by omega,?_,?_⟩
  · have hf := Nat.floor_le (by linarith : 0 ≤ a/(2*δ))
    have hh := (le_div_iff₀ (by positivity)).mp hf
    nlinarith
  · have hf := Nat.lt_floor_add_one (a/(2*δ))
    have hn : (1:ℝ) ≤ ⌊a/(2*δ)⌋₊ := by exact_mod_cast hp
    have hh : a/(2*δ) ≤ 2*⌊a/(2*δ)⌋₊ := by linarith
    have := (div_le_iff₀ (by positivity)).mp hh
    nlinarith

variable {I : Type*} [LinearOrder I]

theorem captured_rich_centers (F : Finset I) (hF : F.Nonempty)
    (P : I → Submodule K V) (X : Finset (ℙ K V))
    (hP : ∀ i ∈ F, finrank K (P i) = 3)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 2)
    (J M : ℕ) (hM : 0 < M) (hJM : J ≤ M)
    (hJq : (J:ℝ)*(Nat.card K:ℝ) ≤ X.card)
    (O : ℙ K V → Finset (ℙ K V))
    (hO : ∀ x, ownCell F hF (fun i => flatPoints (P i)) X J x ⊆ O x)
    (δ a : ℝ) (hδ : 0 < δ) (ha : 2*δ*M ≤ a) (ha' : a ≤ 4*δ*M) :
    (∑ A ∈ L, ((richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A).card:ℝ))*a^2 ≤
      192*δ^2*(X.card:ℝ)^2 := by
  have ha0 : 0 ≤ a := (by positivity : 0 ≤ 2*δ*M).trans ha
  have hsub (A : Submodule K V) : richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A ⊆
      capturedLineCenters F hF P X J (2*M) A := by
    intro x hx
    obtain ⟨hxA,hx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxA,?_⟩
    have hs : (X \ remaining F hF (fun i => flatPoints (P i)) X J) \ (O x ∪ {x}) ⊆
        (X \ remaining F hF (fun i => flatPoints (P i)) X J) \
          ownCell F hF (fun i => flatPoints (P i)) X J x :=
      Finset.sdiff_subset_sdiff_right _ ((hO x).trans Finset.subset_union_left)
    have hc : ((((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        (O x ∪ {x})).filter fun y => y.submodule ≤ A).card:ℝ) ≤
        (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter
          fun y => y.submodule ≤ A).card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hs)
    have hh := ha.trans (hx.trans (mul_le_mul_of_nonneg_left hc hδ.le))
    have hm : ((2*M:ℕ):ℝ) ≤ (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
        ownCell F hF (fun i => flatPoints (P i)) X J x).filter
          fun y => y.submodule ≤ A).card := by
      push_cast
      nlinarith
    exact_mod_cast hm
  have hsum : (∑ A ∈ L, ((richCenters
      (X \ remaining F hF (fun i => flatPoints (P i)) X J) O δ a A).card:ℝ)) ≤
      ∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ) := by
    apply Finset.sum_le_sum
    intro A _
    exact_mod_cast Finset.card_le_card (hsub A)
  have hc := captured_center_line_count F hF P X hP L hL J M hM hJM hJq
  have ha2 := pow_le_pow_left₀ ha0 ha' 2
  calc
    _ ≤ (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*a^2 :=
      mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ ≤ (∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(4*δ*M)^2 :=
      mul_le_mul_of_nonneg_left ha2 (Finset.sum_nonneg fun _ _ => by positivity)
    _ = 16*δ^2*((∑ A ∈ L, ((capturedLineCenters F hF P X J (2*M) A).card:ℝ))*(M:ℝ)^2) := by ring
    _ ≤ 16*δ^2*(12*(X.card:ℝ)^2) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end SharpRamseyFive.GlobalRadial

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MomentWeightedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_weighted_cover (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (hx : ∀ v,0≤x v) (ha : ∀ i∈T,0≤a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i) :
    (∑ v,x v^K)≤2^K*∑ i∈T,
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K := by
  have hp (v : α) : x v^K≤∑ i∈T,if a i≤x v then (2*a i)^K else 0 := by
    by_cases hv : 0<x v
    · obtain ⟨i,hi,hix,hxi⟩:=hcover v hv
      apply (pow_le_pow_left₀ (hx v) hxi K).trans
      have hs:=Finset.single_le_sum (f := fun j => if a j≤x v then (2*a j)^K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa only [ite_eq_left hix] using hs
    · have hz : x v=0 := le_antisymm (le_of_not_gt hv) (hx v)
      rw [hz,zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hp v)).trans_eq
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (∑ v,if a i≤x v then (2*a i)^K else 0)=
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*(2*a i)^K := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he,mul_pow]
  ring

end SharpRamseyFive.DyadicMoments

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_emptyEvent (s : Finset ι) : MeasurableSet (emptyEvent s) := by
  exact MeasurableSet.pi (s.finite_toSet.countable) (fun _ _ => measurableSet_singleton 0)

omit [DecidableEq ι] in
lemma measure_emptyEvent (rate : ι → ℝ≥0) (s : Finset ι) :
    batchMeasure rate (emptyEvent s) = ENNReal.ofReal (Real.exp (-mass rate s)) := by
  rw [batchMeasure, emptyEvent, Measure.pi_pi_finset]
  simp_rw [poissonMeasure_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl
omit [DecidableEq ι] in

lemma integral_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    ∫ ω, emptyIndicator s ω ∂batchMeasure rate = Real.exp (-mass rate s) := by
  simp only [emptyIndicator]
  rw [integral_indicator_const _ (measurableSet_emptyEvent s),
    Measure.real, measure_emptyEvent, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp
omit [DecidableEq ι] in

lemma integrable_emptyIndicator (rate : ι → ℝ≥0) (s : Finset ι) :
    Integrable (emptyIndicator s) (batchMeasure rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_emptyEvent s)

lemma one_sub_exp_neg_le (a : ℝ) : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_IntegralTypicalScoreSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

omit [DecidableEq ι] in
lemma integrable_schedule_of_abs_le (rate : ι → ℝ≥0) {R : ℕ}
    (f : (Fin R → ι → ℕ) → ℝ) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) :
    Integrable f (scheduleMeasure rate R) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using h ω)

omit [Fintype ι] [DecidableEq ι] in
lemma hitIndicator_eq (i : ι) (ω : ι → ℕ) :
    hitIndicator i ω = if ω i = 0 then 0 else 1 := by
  simp only [hitIndicator, emptyIndicator, emptyEvent
    ]
  by_cases h : ω i = 0 <;> simp [h]
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_nonneg (i : ι) (ω : ι → ℕ) : 0 ≤ hitIndicator i ω := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [Fintype ι] [DecidableEq ι] in

lemma hitIndicator_le_one (i : ι) (ω : ι → ℕ) : hitIndicator i ω ≤ 1 := by
  rw [hitIndicator_eq]; split <;> norm_num
omit [DecidableEq ι] in

lemma integral_hitIndicator (rate : ι → ℝ≥0) (i : ι) :
    (∫ ω, hitIndicator i ω ∂batchMeasure rate) = 1 - Real.exp (-(rate i : ℝ)) := by
  unfold hitIndicator
  rw [integral_sub (integrable_const 1) (integrable_emptyIndicator rate {i}),
    integral_emptyIndicator]
  simp [mass]
omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_nonneg {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    0 ≤ forcedHits i T ω := Finset.prod_nonneg (fun _ _ => hitIndicator_nonneg _ _)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
omit [Fintype ι] [DecidableEq ι] in
lemma forcedHits_le_one {R : ℕ} (i : ι) (T : Finset (Fin R)) (ω : Fin R → ι → ℕ) :
    forcedHits i T ω ≤ 1 := Finset.prod_le_one (fun _ _ => hitIndicator_nonneg _ _)
      (fun _ _ => hitIndicator_le_one _ _)

omit [Fintype ι] [DecidableEq ι] in

lemma forcedHits_eq_one_of_subset {R : ℕ} (i : ι) (T : Finset (Fin R))
    (ω : Fin R → ι → ℕ) (h : T ⊆ hitBatches i ω) : forcedHits i T ω = 1 := by
  apply Finset.prod_eq_one
  intro r hr
  rw [hitIndicator_eq]
  have hz : ω r i ≠ 0 := (Finset.mem_filter.mp (h hr)).2
  simp [hz]
omit [Fintype ι] [DecidableEq ι] in

lemma overload_indicator_le_certificates {R : ℕ} (s : Finset ι) (J : ℕ)
    (ω : Fin R → ι → ℕ) :
    (overloaded s J).indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ i ∈ s, ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
  have hnonneg : ∀ i, 0 ≤ ∑ T ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i T ω := by
    intro i
    exact Finset.sum_nonneg (fun T _ => forcedHits_nonneg i T ω)
  by_cases h : ω ∈ overloaded s J
  · rw [Set.indicator_of_mem h]
    obtain ⟨i, hi, hcard⟩ := h
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hcard
    have hTm : T ∈ (Finset.univ : Finset (Fin R)).powersetCard J := by
      simp only [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hTc⟩
    calc
      1 = forcedHits i T ω := (forcedHits_eq_one_of_subset i T ω hT).symm
      _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin R)).powersetCard J, forcedHits i U ω :=
        Finset.single_le_sum (fun U _ => forcedHits_nonneg i U ω) hTm
      _ ≤ _ := Finset.single_le_sum (fun i _ => hnonneg i) hi
  · rw [Set.indicator_of_notMem h]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)

omit [DecidableEq ι] in
lemma measurePreserving_uncurry_schedule (rate : ι → ℝ≥0) (R : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin R) ι ℕ).symm
      (scheduleMeasure rate R) (batchMeasure (fun p : Fin R × ι => rate p.2)) := by
  refine ⟨(MeasurableEquiv.curry (Fin R) ι ℕ).symm.measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi, scheduleMeasure, batchMeasure] using
    Measure.infinitePi_map_curry_symm (fun (_ : Fin R) i => poissonMeasure (rate i))

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.DyadicMoments

open scoped BigOperators

lemma dyadic_cover (δ x : ℝ) (hδ : 0 ≤ δ) (hx : δ ≤ x) (N : ℕ)
    (hN : x ≤ δ * 2 ^ N) :
    ∃ i ∈ Finset.range (N + 1), δ * 2 ^ i ≤ x ∧ x ≤ 2 * (δ * 2 ^ i) := by
  induction N with
  | zero =>
    refine ⟨0, by simp, ?_, ?_⟩
    · simpa using hx
    · simp only [pow_zero, mul_one] at hN ⊢
      linarith
  | succ N ih =>
    by_cases hh : x ≤ δ * 2 ^ N
    · obtain ⟨i, hi, hix, hxi⟩ := ih hh
      exact ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), hix, hxi⟩
    · refine ⟨N, Finset.mem_range.mpr (by omega), le_of_lt (lt_of_not_ge hh), ?_⟩
      rw [pow_succ] at hN
      nlinarith

end SharpRamseyFive.DyadicMoments

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (K : ℕ) (hK : K≠0) (A : ℝ) (hx : ∀ v,0 ≤ x v) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i ≤ x v ∧ x v ≤ 2*a i)
    (hcount : ∀ i∈T,((Finset.univ.filter fun v => a i ≤ x v).card:ℝ)*a i^K ≤ A) :
    (∑ v,x v^K) ≤ 2^K*T.card*A := by
  apply (moment_weighted_cover x a T K hK hx ha hcover).trans
  have hh := Finset.sum_le_sum (fun i hi => hcount i hi)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

theorem pow_sum_from_lower (x : α → ℝ) (m A : ℝ) (K R : ℕ) (hm0 : 0 ≤ m) (hKR : K ≤ R)
    (hx : ∀ v,0 ≤ x v) (hm : ∀ v,x v ≤ m) (hA : (∑ v,x v^K) ≤ A) :
    (∑ v,x v^R) ≤ m^(R-K)*A := by
  have hpow (v : α) : x v^R ≤ m^(R-K)*x v^K := by
    have he : R=(R-K)+K := by omega
    calc
      _ = x v^(R-K)*x v^K := by rw [←pow_add,←he]
      _  ≤  _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hx v) (hm v) _) (pow_nonneg (hx v) _)
  apply (Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpow v)).trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hA (pow_nonneg hm0 _)

end SharpRamseyFive.DyadicMoments

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LocalLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma sum_localLines_le (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V)) :
    ∑ x ∈ Q, (localLines S O δ a L x).card ≤
      ∑ A ∈ L, (richCenters S O δ a A).card := by
  simp_rw [localLines,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro A _
  rw [←Finset.card_filter]
  have hs : Q.filter (fun x => x ∈ richCenters S O δ a A) ⊆ richCenters S O δ a A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  exact Finset.card_le_card hs

end SharpRamseyFive.GlobalRadial
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_filter_card (S O : Finset (ℙ K V)) (A : Submodule K V) :
    ((outsideAt x S O).filter fun y => y.val.submodule ≤ A).card =
      ((S \ (O ∪ {x})).filter fun y => y.submodule ≤ A).card := by
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    have hm : y.val ∈ S \ O := Finset.mem_subtype.mp hy
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton]
    exact ⟨⟨(Finset.mem_sdiff.mp hm).1,not_or.mpr
      ⟨(Finset.mem_sdiff.mp hm).2,Ne.symm y.property⟩⟩,hyA⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨hy,hyA⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyS,hyO⟩ := Finset.mem_sdiff.mp hy
    have hn : x ≠ y := by
      intro he
      exact hyO (Finset.mem_union_right _ (Finset.mem_singleton.mpr he.symm))
    refine ⟨⟨y,hn⟩,Finset.mem_filter.mpr ⟨?_,hyA⟩,rfl⟩
    exact Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr
      ⟨hyS,fun h => hyO (Finset.mem_union_left _ h)⟩)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OutsideCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_card_le (S O : Finset (ℙ K V)) : (outsideAt x S O).card ≤ S.card := by
  unfold outsideAt
  rw [Finset.card_subtype]
  exact (Finset.card_filter_le _ _).trans (Finset.card_le_card Finset.sdiff_subset)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TrainingLineCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [Fintype (RadialLine x)] in
lemma training_line_card (X : Finset {y : ℙ K V // x≠y}) (l : RadialLine x) :
    (RadialLine.trainingOnLine X l).card ≤ Nat.card K+1 := by
  let : Finite V := Module.finite_of_finite K
  let f (y : RadialLine.trainingOnLine X l) : {p : ℙ K V // p.submodule ≤ l.val} :=
    ⟨y.val.val,(Finset.mem_filter.mp y.property).2⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : {p : ℙ K V // p.submodule ≤ l.val} => u.val) he
  have hc := Nat.card_le_card_of_injective f hf
  rw [card_subspacePoints,l.property.1,Nat.card_eq_fintype_card,Fintype.card_coe] at hc
  simpa [Finset.sum_range_succ,Nat.add_comm] using hc

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveHighCapturedMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma radial_bounded_cover (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (M : ℝ) (hmax : ∀ l : RadialLine x,(radialWeight x X δ l:ℝ) ≤ M)
    (l : RadialLine x) (hp : 0 < (radialWeight x X δ l:ℝ)) :
    ∃ i∈boundedOverlapDyads x X δ M,
      (δ:ℝ)*2^i ≤ (radialWeight x X δ l:ℝ) ∧
      (radialWeight x X δ l:ℝ) ≤ 2*((δ:ℝ)*2^i) := by
  have hc : 0 < (RadialLine.trainingOnLine X l).card := by
    by_contra hn
    have hz : (RadialLine.trainingOnLine X l).card=0 := by omega
    simp [radialWeight,hz] at hp
  have hfloor : (δ:ℝ) ≤ (radialWeight x X δ l:ℝ) := by
    have hh : (1:ℝ) ≤ (RadialLine.trainingOnLine X l).card := by exact_mod_cast hc
    simpa only [radialWeight,NNReal.coe_mul,NNReal.coe_natCast,mul_one] using
      mul_le_mul_of_nonneg_left hh δ.coe_nonneg
  have hbound : (radialWeight x X δ l:ℝ) ≤ (δ:ℝ)*2^Nat.clog 2 X.card := by
    have hh : (RadialLine.trainingOnLine X l).card ≤ 2^Nat.clog 2 X.card :=
      (Finset.card_filter_le _ _).trans (Nat.le_pow_clog (by norm_num) X.card)
    change (δ:ℝ)*((RadialLine.trainingOnLine X l).card:ℝ) ≤ (δ:ℝ)*(2:ℝ)^Nat.clog 2 X.card
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) δ.coe_nonneg
  obtain ⟨i,hi,hlo,hhi⟩ := dyadic_cover δ _ δ.coe_nonneg hfloor _ hbound
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,hlo.trans (hmax l)⟩,hlo,hhi⟩

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentCutoffPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_cutoff_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (θ M A : ℝ) (K R : ℕ) (hK : K≠0) (hKR : K≤R)
    (hθ : 0≤θ) (hM : 0≤M) (hA : 0≤A)
    (hx : ∀ v,0≤x v) (hmax : ∀ v,x v≤M) (ha : ∀ i∈T,0<a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i)
    (htail : ∀ i∈T,θ≤2*a i →
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K≤A) :
    (∑ v,x v^R) ≤ (Fintype.card α:ℝ)*θ^R + M^(R-K)*(2^K*T.card*A) := by
  let y (v : α) : ℝ := if θ≤x v then x v else 0
  let U := T.filter fun i => θ≤2*a i
  have hy (v : α) : 0≤y v := by dsimp [y]; split_ifs; exact hx v; rfl
  have hym (v : α) : y v≤M := by dsimp [y]; split_ifs; exact hmax v; exact hM
  have hbase : (∑ v,y v^K) ≤ 2^K*U.card*A := by
    apply moment_polynomial_tail y a U K hK A hy
      (fun i hi => (ha i (Finset.mem_filter.mp hi).1).le)
    · intro v hv
      have hv' : θ≤x v := by by_contra hn; simp [y,hn] at hv
      have hpos : 0<x v := by simpa [y,hv'] using hv
      obtain ⟨i,hi,hlo,hhi⟩ := hcover v hpos
      exact ⟨i,Finset.mem_filter.mpr ⟨hi,hv'.trans hhi⟩,by simpa [y,hv'] using hlo,
        by simpa [y,hv'] using hhi⟩
    · intro i hi
      have hiT := (Finset.mem_filter.mp hi).1
      have hc : (Finset.univ.filter fun v => a i≤y v).card ≤
          (Finset.univ.filter fun v => a i≤x v).card := by
        apply Finset.card_le_card
        intro v hv
        have hv' := (Finset.mem_filter.mp hv).2
        have hyx : y v≤x v := by dsimp [y]; split_ifs; rfl; exact hx v
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv'.trans hyx⟩
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc)
        (pow_nonneg (ha i hiT).le K)).trans (htail i hiT (Finset.mem_filter.mp hi).2)
  have hbase' : (∑ v,y v^K) ≤ 2^K*T.card*A := by
    apply hbase.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.card_filter_le T _)) (by positivity)) hA
  have hhi := pow_sum_from_lower y M _ K R hM hKR hy hym hbase'
  have hpoint (v : α) : x v^R ≤ θ^R+y v^R := by
    by_cases hv : θ≤x v
    · simpa [y,hv] using (le_add_of_nonneg_left (a := x v^R) (pow_nonneg hθ R))
    · have hp := pow_le_pow_left₀ (hx v) (le_of_not_ge hv) R
      exact hp.trans (le_add_of_nonneg_right (pow_nonneg (hy v) R))
  calc
    _ ≤ ∑ v,(θ^R+y v^R) := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = (Fintype.card α:ℝ)*θ^R+∑ v,y v^R := by simp [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add_right hhi _

end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma radial_tail_le_localLines (x : ℙ K V) [Fintype (RadialLine x)]
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (hLines : ∀ l : RadialLine x,l.val∈Lines) :
    (Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)).card ≤
      (localLines S O δ a Lines x).card := by
  let A := Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)
  let E := localLines S O δ a Lines x
  let f (l : A) : E := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hLines l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      change a ≤ (δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule ≤ l.val.val).card:ℝ) at hr
      rwa [outsideAt_filter_card] at hr⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : E => z.val) he))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [∀ x : ℙ K V,Fintype (RadialLine x)]

lemma global_radial_tail (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines) :
    (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
      a ≤ (radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2:ℝ)).card ≤
      ∑ A∈Lines,(richCenters S O δ a A).card := by
  have he : (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
      a ≤ (radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2:ℝ)).card =
      ∑ x : Q,(Finset.univ.filter fun l : RadialLine x.val =>
        a ≤ (radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)).card := by
    simp only [Finset.card_filter,Fintype.sum_sigma]
  rw [he]
  calc
    _ ≤ ∑ x : Q,(localLines S O δ a Lines x.val).card :=
      Finset.sum_le_sum fun x _ => radial_tail_le_localLines x.val S O δ a Lines (hLines x.val x.property)
    _ = ∑ x∈Q,(localLines S O δ a Lines x).card := Finset.sum_coe_sort Q (fun x => (localLines S O δ a Lines x).card)
    _ ≤ _ := sum_localLines_le S O δ a Lines Q

theorem global_radial_moment (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0<δ) (θ A : ℝ) (hθ : 0≤θ) (hA : 0≤A)
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (htail : ∀ i∈Finset.range (Nat.clog 2 S.card+1),θ≤2*((δ:ℝ)*2^i) →
      (δ:ℝ)*2^i≤(δ:ℝ)*((Nat.card K:ℝ)+1) →
      (∑ l∈Lines,((richCenters S O δ ((δ:ℝ)*2^i) l).card:ℝ))*((δ:ℝ)*2^i)^2≤A)
    (J : ℕ) (hJ : 2≤J) :
    (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) ≤
      (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))*θ^J+
        ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-2)*(4*(Nat.clog 2 S.card+1)*A) := by
  let w (z : Σ x : Q,RadialLine x.val) : ℝ :=
    radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2
  have hw (z : Σ x : Q,RadialLine x.val) : 0≤w z := NNReal.coe_nonneg _
  have hmax (z : Σ x : Q,RadialLine x.val) : w z≤(δ:ℝ)*((Nat.card K:ℝ)+1) := by
    have hc := training_line_card z.1.val (outsideAt z.1.val S (O z.1.val)) z.2
    change (δ:ℝ)*((RadialLine.trainingOnLine _ _).card:ℝ) ≤ _
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) δ.coe_nonneg
  have hcS (x : ℙ K V) : (outsideAt x S (O x)).card≤S.card := outsideAt_card_le x S (O x)
  have hcover (z : Σ x : Q,RadialLine x.val) (hp : 0<w z) :
      ∃ i∈Finset.range (Nat.clog 2 S.card+1),(δ:ℝ)*2^i≤w z ∧ w z≤2*((δ:ℝ)*2^i) := by
    obtain ⟨i,hi,hlo,hhi⟩ := radial_bounded_cover z.1.val (outsideAt z.1.val S (O z.1.val)) δ
      ((δ:ℝ)*((Nat.card K:ℝ)+1)) (fun l => hmax ⟨z.1,l⟩) z.2 hp
    refine ⟨i,?_,hlo,hhi⟩
    have hir := (Finset.mem_filter.mp hi).1
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hir
    exact lt_of_lt_of_le this (Nat.add_le_add_right (Nat.clog_mono_right 2 (hcS z.1.val)) 1)
  have hh := moment_cutoff_polynomial_tail w (fun i : ℕ => (δ:ℝ)*2^i)
    (Finset.range (Nat.clog 2 S.card+1)) θ ((δ:ℝ)*((Nat.card K:ℝ)+1)) A 2 J
    (by norm_num) hJ hθ (by positivity) hA hw hmax
    (by intro i _; positivity) hcover (by
      intro i hi hcut
      by_cases hcap : (δ:ℝ)*2^i≤(δ:ℝ)*((Nat.card K:ℝ)+1)
      · have ht := global_radial_tail S O δ ((δ:ℝ)*2^i) Lines Q hLines
        have htr : ((Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
            (δ:ℝ)*2^i≤w z).card:ℝ) ≤
            ∑ l∈Lines,((richCenters S O δ ((δ:ℝ)*2^i) l).card:ℝ) := by
          exact_mod_cast ht
        exact (mul_le_mul_of_nonneg_right htr (sq_nonneg _)).trans (htail i hi hcut hcap)
      · have he : (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val => (δ:ℝ)*2^i≤w z)=∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro z hz
          exact hcap ((Finset.mem_filter.mp hz).2.trans (hmax z))
        simpa only [he,Finset.card_empty,Nat.cast_zero,zero_mul] using hA)
  simpa only [Fintype.sum_sigma,Finset.card_range,Nat.cast_add,Nat.cast_one,
    Fintype.card_sigma,Nat.cast_sum,show (2:ℝ)^2=4 by norm_num] using hh

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_IntegralForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma integral_forcedHits_le (rate : D→ℝ≥0) {R : ℕ} (d : D) (T : Finset (Fin R)) :
    (∫ ω,forcedHits d T ω ∂scheduleMeasure rate R) ≤ (rate d:ℝ)^T.card := by
  have he (ω : Fin R→D→ℕ) : forcedHits d T ω =
      ∏ r : Fin R,if r∈T then hitIndicator d (ω r) else 1 := by
    simp only [Finset.prod_ite_mem,Finset.univ_inter,forcedHits]
  simp_rw [he]
  unfold scheduleMeasure
  rw [integral_fintype_prod_eq_prod (f := fun r ω => if r∈T then hitIndicator d ω else 1)]
  have he' (r : Fin R) : (∫ ω : D→ℕ,(if r∈T then hitIndicator d ω else 1) ∂batchMeasure rate) =
      if r∈T then 1-Real.exp (-(rate d:ℝ)) else 1 := by
    split_ifs <;> simp [integral_hitIndicator]
  simp_rw [he']
  simp only [Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_const]
  exact pow_le_pow_left₀ (by have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rate d).coe_nonneg); linarith)
    (one_sub_exp_neg_le (rate d:ℝ)) _

omit [DecidableEq D] in
theorem overload_probability (rate : D→ℝ≥0) {R : ℕ} (s : Finset D) (J : ℕ) :
    (scheduleMeasure rate R).real (overloaded s J) ≤ ∑ d∈s,((R:ℝ)*(rate d:ℝ))^J := by
  have hint := integrable_schedule_of_abs_le (R := R) rate
    ((overloaded s J).indicator (fun _ => (1:ℝ))) 1 (by
      intro ω; by_cases he : ω∈overloaded s J <;> simp [he])
  have hf (d : D) (T : Finset (Fin R)) : Integrable (forcedHits d T) (scheduleMeasure rate R) :=
    integrable_schedule_of_abs_le rate _ 1 (fun ω => by
      rw [abs_of_nonneg (forcedHits_nonneg d T ω)]; exact forcedHits_le_one d T ω)
  have hset : MeasurableSet (overloaded s J : Set (Fin R→D→ℕ)) := Set.to_countable _ |>.measurableSet
  have heq := integral_indicator_const (μ := scheduleMeasure rate R) (1:ℝ) hset
  simp only [smul_eq_mul,mul_one] at heq
  rw [←heq]
  calc
    _ ≤ ∫ ω,∑ d∈s,∑ T∈(Finset.univ : Finset (Fin R)).powersetCard J,forcedHits d T ω
        ∂scheduleMeasure rate R := integral_mono hint
          (integrable_finsetSum _ (fun d _ => integrable_finsetSum _ (fun T _ => hf d T)))
          (overload_indicator_le_certificates s J)
    _ = ∑ d∈s,∑ T∈(Finset.univ : Finset (Fin R)).powersetCard J,
        ∫ ω,forcedHits d T ω ∂scheduleMeasure rate R := by
      rw [integral_finsetSum _ (fun d _ => integrable_finsetSum _ (fun T _ => hf d T))]
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_finsetSum _ (fun T _ => hf d T)]
    _ ≤ ∑ d∈s,((R:ℝ)*(rate d:ℝ))^J := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        _ ≤ ∑ _T∈(Finset.univ : Finset (Fin R)).powersetCard J,(rate d:ℝ)^J :=
          Finset.sum_le_sum fun T hT => by
            simpa only [(Finset.mem_powersetCard.mp hT).2] using integral_forcedHits_le rate d T
        _ = (R.choose J:ℝ)*(rate d:ℝ)^J := by simp
        _ ≤ _ := by
          rw [mul_pow]
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (rate d).coe_nonneg _)
          exact_mod_cast Nat.choose_le_pow R J

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.HighMoment
open MeasureTheory ProbabilityTheory PoissonScore TupleComponents
open scoped BigOperators NNReal Classical
variable {D : Type} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma allTrunc_indicator (R J : ℕ) (ω : Fin R→D→ℕ) :
    1-allTrunc R J (Function.uncurry ω) =
      (overloaded Finset.univ J).indicator (fun _ => (1:ℝ)) ω := by
  by_cases he : ω∈(overloaded Finset.univ J : Set (Fin R→D→ℕ))
  · rw [Set.indicator_of_mem he]
    obtain ⟨d,_,hd⟩ := he
    have hz : allTrunc R J (Function.uncurry ω)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ d)
      exact ite_eq_right (by exact not_lt.mpr hd)
    rw [hz,sub_zero]
  · rw [Set.indicator_of_notMem he]
    have ho : allTrunc R J (Function.uncurry ω)=1 := by
      apply Finset.prod_eq_one
      intro d _
      apply ite_eq_left
      by_contra hn
      exact he ⟨d,Finset.mem_univ _,le_of_not_gt hn⟩
    rw [ho,sub_self]

omit [DecidableEq D] in
theorem allTrunc_failure (rate : D→ℝ≥0) (R J : ℕ) :
    (∫ ω,1-allTrunc R J ω ∂batchMeasure (fun p : Fin R×D => rate p.2)) ≤
      ∑ d : D,((R:ℝ)*(rate d:ℝ))^J := by
  rw [←(measurePreserving_uncurry_schedule rate R).integral_comp' (fun ω => 1-allTrunc R J ω)]
  change (∫ ω,1-allTrunc R J (Function.uncurry ω) ∂scheduleMeasure rate R) ≤ _
  simp_rw [allTrunc_indicator]
  have hset : MeasurableSet (overloaded Finset.univ J : Set (Fin R→D→ℕ)) := Set.to_countable _ |>.measurableSet
  rw [integral_indicator_const (1:ℝ) hset]
  simp only [smul_eq_mul,mul_one]
  exact overload_probability rate Finset.univ J

end SharpRamseyFive.HighMoment

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CapturedGlobalRadialMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [∀ x : ℙ K V,Fintype (RadialLine x)]

theorem captured_global_radial_moment {I : Type} [LinearOrder I]
    (F : Finset I) (hF : F.Nonempty) (P : I→Submodule K V) (X S : Finset (ℙ K V))
    (hP : ∀ i∈F,finrank K (P i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (P i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀ x,ownCell F hF (fun i => flatPoints (P i)) X j x⊆O x)
    (δ : ℝ≥0) (hδ : 0<δ) (θ : ℝ) (hθ : 8*(δ:ℝ)*(j+1)≤θ)
    (Lines : Finset (Submodule K V)) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (J : ℕ) (hJ : 2≤J) :
    (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) ≤
      (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))*θ^J+
        ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-2)*
          (4*(Nat.clog 2 S.card+1)*(192*(δ:ℝ)^2*(X.card:ℝ)^2)) := by
  have hδ' : 0<(δ:ℝ) := hδ
  have hθ0 : 0≤θ := (by positivity : 0≤8*(δ:ℝ)*(j+1)).trans hθ
  apply global_radial_moment S O δ hδ θ _ hθ0 (by positivity) Lines Q hLines _ J hJ
  intro i hi hcut _hmax
  let a : ℝ := (δ:ℝ)*2^i
  have hscale : 4*(δ:ℝ)≤a := by
    have hj0 : (0:ℝ)≤j := Nat.cast_nonneg j
    change θ≤2*a at hcut
    nlinarith
  obtain ⟨M,hM,hlo,hhi⟩ := exists_scale hδ' hscale
  have hjM : j≤M := by
    have hjM' : (j:ℝ)≤M := by
      change θ≤2*a at hcut
      nlinarith
    exact_mod_cast hjM'
  have hm := captured_rich_centers F hF P X hP Lines hrank j M hM hjM hj O hO
    δ a hδ' hlo hhi
  have hs : (∑ l∈Lines,((richCenters S O δ a l).card:ℝ)) ≤
      ∑ l∈Lines,((richCenters (X\remaining F hF (fun i => flatPoints (P i)) X j) O δ a l).card:ℝ) := by
    apply Finset.sum_le_sum
    intro l hl
    exact Nat.cast_le.mpr (Finset.card_le_card (richCenters_mono S _ O O δ a δ.coe_nonneg hS
      (fun _ => Finset.Subset.refl _) l))
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg a)).trans hm

open MeasureTheory

omit [FiniteDimensional K V] [Finite K] in
theorem global_trunc_failure (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ L : ℝ≥0) (Q : Finset (ℙ K V)) (R J : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R J ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val S (O x.val)) δ p.2)) ≤
      ((R:ℝ)*(L:ℝ))^J*
        (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) := by
  calc
    _ ≤ ∑ x : Q,∑ l : RadialLine x.val,((R:ℝ)*
        ((L*radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ≥0):ℝ))^J :=
      Finset.sum_le_sum fun x _ => HighMoment.allTrunc_failure
        (fun l => L*radialWeight x.val (outsideAt x.val S (O x.val)) δ l) R J
    _ = _ := by
      simp only [NNReal.coe_mul,←mul_assoc,mul_pow,Finset.mul_sum]

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DyadCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma dyad_count_le {m : ℕ} {σ : ℝ} (hσ : 1≤σ)
    (hm : (m:ℝ)≤Real.exp (3*σ)) : (Nat.clog 2 m:ℝ)+1≤8*σ := by
  by_cases hm1 : m≤1
  · rw [Nat.clog_of_right_le_one hm1]
    simp only [Nat.cast_zero,zero_add]
    linarith
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hml : 0≤Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmlhi : Real.log (m:ℝ)≤3*σ := (Real.log_le_iff_le_exp hm0).mpr hm
  have hlog : Real.logb 2 (m:ℝ)≤6*σ := by
    rw [Real.logb]
    apply (div_le_iff₀ (by linarith : 0<Real.log 2)).mpr
    nlinarith
  have hc := Nat.ceil_lt_add_one (show 0≤Real.logb 2 (m:ℝ) by
    rw [Real.logb]; exact div_nonneg hml (by linarith))
  have he := Real.natCeil_logb_natCast 2 m
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hc
  linarith

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometryScaleOrientedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

open Filter ParameterHierarchy
open scoped Topology

lemma global_radial_numeric {σ g N M A θ : ℝ} {m : ℕ}
    (hσ : 1≤σ) (_hN0 : 0≤N) (hM0 : 0≤M) (hA0 : 0≤A) (hθ0 : 0≤θ)
    (hN : N≤4*Real.exp (8*σ)) (hM : M≤8*Real.exp (-g))
    (hA : A≤333024*Real.exp (2*σ))
    (hθ : θ≤2*Real.exp (-(g+σ/2)/20)) (hm : (m:ℝ)≤Real.exp (3*σ)) :
    N*θ^5000+M^4998*(4*((Nat.clog 2 m:ℝ)+1)*A) ≤
      globalTruncConstant*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*σ*Real.exp (2*σ-4998*g) := by
  have hc1 : 4*(2:ℝ)^5000≤globalTruncConstant := by
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hc2 : 32*333024*(8:ℝ)^4998≤globalTruncConstant := by
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hdy := dyad_count_le hσ hm
  apply add_le_add
  · calc
      _ ≤ (4*Real.exp (8*σ))*(2*Real.exp (-(g+σ/2)/20))^5000 :=
        mul_le_mul hN (pow_le_pow_left₀ hθ0 hθ _) (pow_nonneg hθ0 _) (by positivity)
      _ = (4*2^(5000:ℕ))*Real.exp (8*σ-250*(g+σ/2)) := by
        rw [mul_pow,←Real.exp_nat_mul]
        simp only [Nat.cast_ofNat]
        rw [show 4*Real.exp (8*σ)*(2^(5000:ℕ)*Real.exp (5000*(-(g+σ/2)/20))) =
          (4*2^(5000:ℕ))*(Real.exp (8*σ)*Real.exp (5000*(-(g+σ/2)/20))) by ac_rfl]
        rw [←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc1 (Real.exp_nonneg _)
  · calc
      _ ≤ (8*Real.exp (-g))^4998*(4*(8*σ)*(333024*Real.exp (2*σ))) := by
        apply mul_le_mul (pow_le_pow_left₀ hM0 hM _) _ (by positivity) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hdy (by norm_num)) hA hA0 (by positivity)
      _ = (32*333024*8^(4998:ℕ))*σ*Real.exp (2*σ-4998*g) := by
        rw [mul_pow,←Real.exp_nat_mul]
        simp only [Nat.cast_ofNat]
        rw [show 8^(4998:ℕ)*Real.exp (4998*(-g))*(4*(8*σ)*(333024*Real.exp (2*σ))) =
          (32*333024*8^(4998:ℕ))*σ*(Real.exp (2*σ)*Real.exp (4998*(-g))) by
            rw [show (32:ℝ)=4*8 by norm_num]
            ac_rfl]
        rw [←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (by linarith)) (Real.exp_nonneg _)

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighGeometryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

omit [FiniteDimensional K V] [Finite K] in
lemma RadialLine.exists_other (x : ℙ K V) (l : RadialLine x) :
    ∃ y : ℙ K V,x≠y ∧ y.submodule≤l.val := by
  have hn : ¬l.val≤x.submodule := by
    intro h
    have hh := Submodule.finrank_mono h
    rw [l.property.1,x.finrank_submodule] at hh
    omega
  obtain ⟨v,hv,hvx⟩ := SetLike.not_le_iff_exists.mp hn
  have hv0 : v≠0 := by intro he; exact hvx (he▸x.submodule.zero_mem)
  refine ⟨Projectivization.mk K v hv0,?_,?_⟩
  · intro he
    apply hvx
    rw [he,Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self v
  · rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    exact hv

omit [Finite K] in
lemma radial_card_le_points (x : ℙ K V) [Fintype (ℙ K V)] [Fintype (RadialLine x)] :
    Fintype.card (RadialLine x)≤Fintype.card (ℙ K V) := by
  let y : RadialLine x→ℙ K V := fun l => (l.exists_other x).choose
  have hy (l : RadialLine x) : x≠y l ∧ (y l).submodule≤l.val :=
    (l.exists_other x).choose_spec
  apply Fintype.card_le_of_injective y
  intro l m he
  have hl : RadialLine.through x (y l) (hy l).1=l :=
    (RadialLine.through_eq_iff (hy l).1 l).mpr (hy l).2
  have hm : RadialLine.through x (y l) (hy l).1=m :=
    (RadialLine.through_eq_iff (hy l).1 m).mpr (he▸(hy m).2)
  exact hl.symm.trans hm

lemma center_radial_count_le [Fintype (ℙ K V)] [∀ x : ℙ K V,Fintype (RadialLine x)]
    {d : ℕ} (hdim : finrank K V=d+1) (hq : 2≤Nat.card K)
    (Q : Finset (ℙ K V)) :
    (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))≤4*(Nat.card K:ℝ)^(2*d) := by
  have hcard := projective_card_le_two_pow hdim hq
  have hQ : Q.card≤2*Nat.card K^d := (Finset.card_le_univ Q).trans hcard
  calc
    _ ≤ ∑ _x : Q,(2*(Nat.card K:ℝ)^d) := Finset.sum_le_sum fun x _ => by
      exact_mod_cast (radial_card_le_points x.val).trans hcard
    _ = (Q.card:ℝ)*(2*(Nat.card K:ℝ)^d) := by simp
    _ ≤ (2*(Nat.card K:ℝ)^d)*(2*(Nat.card K:ℝ)^d) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (by positivity)
    _ = _ := by rw [mul_comm 2 d,pow_mul]; ring

end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.ScoreGeometry

section
open Filter ParameterHierarchy
open scoped Topology

lemma high_density_bounds {σ g q n δ X : ℝ} (hσ : 0≤σ) (hδ : 0≤δ)
    (hq : q=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hX0 : 0≤X) (hX : X≤n) (hscale : n*δ≤4*q) :
    δ*(q+1)≤8*Real.exp (-g) ∧ 192*δ^2*X^2≤333024*Real.exp (2*σ) := by
  have hq1 : 1≤q := hq▸Real.one_le_exp_iff.mpr hσ
  have hn0 : 0<n := hn▸Real.exp_pos _
  have hq2 : q^2=Real.exp (2*σ) := by rw [hq,←Real.exp_nat_mul]; norm_num
  have he : n*(4*Real.exp (-g))=4*q^2 := by
    rw [hn,hq2,mul_left_comm,←Real.exp_add]
    congr 2
    ring
  have hδq : δ*q≤4*Real.exp (-g) := by
    apply (mul_le_mul_iff_right₀ hn0).mp
    calc
      _ = (n*δ)*q := by ring
      _ ≤ (4*q)*q := mul_le_mul_of_nonneg_right hscale (by linarith)
      _ = _ := by rw [he]; ring
  constructor
  · calc
      _ ≤ 2*(δ*q) := by nlinarith
      _ ≤ 2*(4*Real.exp (-g)) := mul_le_mul_of_nonneg_left hδq (by norm_num)
      _ = _ := by ring
  · have hdX : δ*X≤4*q := (mul_le_mul_of_nonneg_left hX hδ).trans (by simpa only [mul_comm] using hscale)
    have hs := pow_le_pow_left₀ (mul_nonneg hδ hX0) hdX 2
    rw [mul_pow,mul_pow] at hs
    rw [←hq2]
    nlinarith [sq_nonneg q]

end

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)]
  [∀ x : ℙ K V,Fintype (RadialLine x)]

theorem captured_global_trunc_exp_bound_oai (hdim : finrank K V=5)
    {I : Type} [LinearOrder I] (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V))
    (hFlat : ∀ i∈F,finrank K (Flat i)=3) (j : ℕ)
    (hS : S⊆X\remaining F hF (fun i => flatPoints (Flat i)) X j)
    (hj : (j:ℝ)*(Nat.card K:ℝ)≤X.card)
    (O : ℙ K V→Finset (ℙ K V))
    (hO : ∀ x,ownCell F hF (fun i => flatPoints (Flat i)) X j x⊆O x)
    (δ L : ℝ≥0) (hδ : 0<δ) (σ g n : ℝ) (hσ : 1≤σ)
    (hq : (Nat.card K:ℝ)=Real.exp σ) (hn : n=Real.exp (2*σ+g))
    (hg : g≤σ) (hX : (X.card:ℝ)≤n) (hscale : n*(δ:ℝ)≤4*Nat.card K)
    (hcut : 8*(δ:ℝ)*(j+1)≤2*Real.exp (-(g+σ/2)/20))
    (Lines : Finset (Submodule K V)) (hrank : ∀ l∈Lines,finrank K l=2)
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (R : ℕ) :
    (∑ x : Q,∫ ω,1-HighMoment.allTrunc R 5000 ω
      ∂batchMeasure (fun p : Fin R×RadialLine x.val =>
        L*radialWeight x.val (outsideAt x.val S (O x.val)) δ p.2)) ≤
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*((R:ℝ)*(L:ℝ))^5000*σ*Real.exp (2*σ-4998*g) := by
  have hqNat : 2≤Nat.card K := Finite.one_lt_card
  have hN := center_radial_count_le (d:=4) hdim hqNat Q
  have heq : (Nat.card K:ℝ)^8=Real.exp (8*σ) := by
    rw [hq,←Real.exp_nat_mul]; norm_num
  norm_num only [show 2*4=8 from rfl] at hN
  rw [heq] at hN
  have hdens := high_density_bounds (by linarith : 0≤σ) δ.coe_nonneg hq hn
    (Nat.cast_nonneg X.card) hX hscale
  have hm : (S.card:ℝ)≤Real.exp (3*σ) := by
    calc
      _ ≤ (X.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card (hS.trans Finset.sdiff_subset))
      _ ≤ n := hX
      _ ≤ _ := hn▸Real.exp_le_exp.mpr (by linarith)
  have hrad := captured_global_radial_moment F hF Flat X S hFlat j hS hj O hO δ hδ
    (2*Real.exp (-(g+σ/2)/20)) hcut Lines hrank Q hLines 5000 (by norm_num)
  simp only [Nat.reduceSub] at hrad
  have hnum := global_radial_numeric hσ (by positivity)
    (mul_nonneg δ.coe_nonneg (by positivity)) (by positivity) (by positivity)
    hN hdens.1 hdens.2 (le_refl _) hm
  have hh := (global_trunc_failure S O δ L Q R 5000).trans
    (mul_le_mul_of_nonneg_left (hrad.trans hnum) (by positivity))
  apply hh.trans_eq
  rw [mul_add]
  ac_rfl

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound_oai := @OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound_oai
