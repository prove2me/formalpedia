-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_fraction_field_trdeg_bound_over_field
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:09:02.826332+00:00
-- url     : https://prove2.me/submissions/94adfc54-ec72-4277-9b5e-9dc31c67db7b

import Mathlib
set_option linter.unusedSectionVars false

universe u
namespace A3S51HVK
open Ideal

theorem maxHeight : ∀ (r : ℕ) (F : Type u) [Field F] (M : Ideal (MvPolynomial (Fin r) F)) [M.IsMaximal],
    M.height = r := by
  intro r
  induction r with
  | zero =>
    intro F _ M _
    let e : MvPolynomial (Fin 0) F ≃+* F := (MvPolynomial.isEmptyAlgEquiv F (Fin 0)).toRingEquiv
    have hM : M = ⊥ := by
      have : (M.map e).IsMaximal := map_isMaximal_of_equiv e
      have h2 : M.map e = ⊥ := (eq_bot_or_top _).resolve_right this.ne_top
      have := Ideal.comap_map_of_bijective e e.bijective (I := M)
      rw [← this, h2, comap_bot_of_injective _ e.injective]
    subst hM
    simp
  | succ r ih =>
    intro F _ M _
    let e : MvPolynomial (Fin (r + 1)) F ≃+* Polynomial (MvPolynomial (Fin r) F) :=
      (MvPolynomial.finSuccEquiv F r).toRingEquiv
    let M' := M.map e
    haveI : M'.IsMaximal := map_isMaximal_of_equiv e
    let p := M'.comap (Polynomial.C)
    haveI : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    haveI : M'.LiesOver p := ⟨rfl⟩
    have h1 := Polynomial.height_eq_height_add_one p M'
    rw [ih F p] at h1
    rw [← e.height_map M, h1]
    norm_cast

end A3S51HVK


namespace A3S51HTK
open Ideal MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {k : Type u} [Field k] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] (s : Finset (Fin n))

abbrev R (k : Type u) [Field k] (n : ℕ) := MvPolynomial (Fin n) k
abbrev K := FractionRing (R k n ⧸ P)
abbrev σ := {i : Fin n // i ∉ s}
abbrev B (k : Type u) [Field k] := MvPolynomial s k
abbrev T (k : Type u) [Field k] := MvPolynomial (σ s) (B s k)
abbrev F (k : Type u) [Field k] := FractionRing (B s k)
abbrev L (k : Type u) [Field k] := MvPolynomial (σ s) (F s k)

noncomputable def eqv : Fin n ≃ σ s ⊕ s :=
  (Equiv.sumCompl (· ∈ s)).symm.trans (Equiv.sumComm _ _)

noncomputable def e0 (k : Type u) [Field k] : R k n ≃ₐ[k] T s k :=
  (renameEquiv k (eqv s)).trans (sumAlgEquiv k (σ s) s)

noncomputable def x (i : Fin n) : K P := algebraMap (R k n) (K P) (X i)

noncomputable def ψ : T s k →+* K P := (algebraMap (R k n) (K P)).comp (e0 s k).symm.toRingEquiv.toRingHom

lemma e0_symm_X (j : σ s) : (e0 s k).symm (X j) = X j.1 := by
  simp [e0, sumAlgEquiv_symm_X, eqv]

lemma e0_symm_CX (i : s) : (e0 s k).symm (C (X i)) = X i.1 := by
  simp [e0, sumAlgEquiv_symm_C_X, eqv]

lemma e0_symm_C (b : B s k) : (e0 s k).symm (C b) = rename Subtype.val b := by
  have : ((e0 s k).symm.toAlgHom.comp (IsScalarTower.toAlgHom k (B s k) (T s k))) =
      rename Subtype.val := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', rename_X]
    exact e0_symm_CX s i
  exact congrArg (fun f => f b) this

lemma ψ_C (b : B s k) : ψ P s (C b) = aeval (fun i : s => x P i.1) b := by
  have : (IsScalarTower.toAlgHom k (R k n) (K P)).comp (rename Subtype.val) =
      aeval (fun i : s => x P i.1) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x]
  change algebraMap (R k n) (K P) ((e0 s k).symm (C b)) = _
  rw [e0_symm_C]
  exact congrArg (fun f => f b) this

lemma ψ_X (j : σ s) : ψ P s (X j) = x P j.1 := by
  change algebraMap (R k n) (K P) ((e0 s k).symm (X j)) = _
  rw [e0_symm_X]; rfl

lemma algebraMap_eq_zero (r : R k n) : algebraMap (R k n) (K P) r = 0 ↔ r ∈ P := by
  rw [IsScalarTower.algebraMap_apply (R k n) (R k n ⧸ P) (K P),
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

lemma ker_ψ : RingHom.ker (ψ P s) = P.comap ((e0 s k).symm.toRingEquiv : T s k →+* R k n) := by
  ext t
  rw [RingHom.mem_ker, Ideal.mem_comap]
  exact algebraMap_eq_zero P _

lemma height_ker_ψ : (RingHom.ker (ψ P s)).height = P.height := by
  rw [ker_ψ]
  exact RingEquiv.height_comap _ P

noncomputable abbrev Msub (k : Type u) [Field k] : Submonoid (T s k) := (nonZeroDivisors (B s k)).map (C (σ := σ s))

variable (hs : AlgebraicIndependent k (fun i : s => x P i.1))
include hs

lemma ψ_ne (m : Msub s k) : ψ P s m ≠ 0 := by
  obtain ⟨_, ⟨b, hb, rfl⟩⟩ := m
  rw [ψ_C]
  intro h
  have : b = 0 := hs.eq_zero_of_aeval_eq_zero b h
  exact nonZeroDivisors.ne_zero hb this

noncomputable def ψL : L s k →+* K P :=
  IsLocalization.lift (M := Msub s k) (S := L s k) (g := ψ P s) fun m => (ψ_ne P s hs m).isUnit

lemma ψL_alg (t : T s k) : ψL P s hs (algebraMap (T s k) (L s k) t) = ψ P s t :=
  IsLocalization.lift_eq _ _

lemma comap_ker_ψL : (RingHom.ker (ψL P s hs)).comap (algebraMap (T s k) (L s k)) = RingHom.ker (ψ P s) := by
  ext t; rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ψL_alg]

lemma height_ker_ψL : (RingHom.ker (ψL P s hs)).height = P.height := by
  haveI : (RingHom.ker (ψ P s)).IsPrime := RingHom.ker_isPrime _
  have h1 := IsLocalization.map_comap (Msub s k) (L s k) (RingHom.ker (ψL P s hs))
  change Ideal.map _ (Ideal.comap _ _) = _ at h1
  rw [comap_ker_ψL] at h1
  rw [← h1, IsLocalization.height_map_of_disjoint (Msub s k), height_ker_ψ]
  rw [Set.disjoint_left]
  intro t ht ht'
  exact ψ_ne P s hs ⟨t, ht⟩ ht'

noncomputable def algF : Algebra (F s k) (K P) :=
  ((ψL P s hs).comp (algebraMap (F s k) (L s k))).toAlgebra

lemma algF_B (b : B s k) :
    (ψL P s hs).comp (algebraMap (F s k) (L s k)) (algebraMap (B s k) (F s k) b) =
      aeval (fun i : s => x P i.1) b := by
  rw [RingHom.comp_apply, ← ψ_C P s, ← ψL_alg P s hs]
  congr 1
  change C (algebraMap (B s k) (F s k) b) = MvPolynomial.map (algebraMap (B s k) (F s k)) (C b)
  rw [map_C]

theorem isMax (htb : IsTranscendenceBasis k (fun i : s => x P i.1)) : (RingHom.ker (ψL P s hs)).IsMaximal := by
  classical
  letI := algF P s hs
  let f : L s k →ₐ[F s k] K P := { ψL P s hs with commutes' := fun _ => rfl }
  have hker : RingHom.ker (ψL P s hs) = RingHom.ker f := rfl
  rw [hker]
  have hinj := Ideal.kerLiftAlg_injective f
  have hX : ∀ j : σ s, IsIntegral (F s k) (Ideal.Quotient.mk (RingHom.ker f) (X j)) := by
    intro j
    apply IsAlgebraic.isIntegral
    rw [← isAlgebraic_algHom_iff (Ideal.kerLiftAlg f) hinj]
    have hfx : Ideal.kerLiftAlg f (Ideal.Quotient.mk (RingHom.ker f) (X j)) = x P j.1 := by
      rw [Ideal.kerLiftAlg_mk]
      change ψL P s hs (X j) = _
      rw [← ψ_X P s j, ← ψL_alg P s hs]
      congr 1
      change X j = MvPolynomial.map (algebraMap (B s k) (F s k)) (X j)
      rw [map_X]
    rw [hfx]
    haveI := htb.isAlgebraic
    have ha : IsAlgebraic (Algebra.adjoin k (Set.range (fun i : s => x P i.1))) (x P j.1) :=
      Algebra.IsAlgebraic.isAlgebraic _
    let g : Algebra.adjoin k (Set.range (fun i : s => x P i.1)) →+* F s k :=
      (algebraMap (B s k) (F s k)).comp (hs.repr : _ →+* B s k)
    have hg : Function.Injective g :=
      (IsFractionRing.injective (B s k) (F s k)).comp hs.aevalEquiv.symm.injective
    have := IsAlgebraic.ringHom_of_comp_eq (f := g) (g := RingHom.id (K P)) ha hg (by
      ext a
      change (ψL P s hs).comp (algebraMap (F s k) (L s k)) (algebraMap (B s k) (F s k) (hs.repr a)) = _
      rw [algF_B, hs.aeval_repr]
      rfl)
    exact this
  have hint : Algebra.IsIntegral (F s k) (L s k ⧸ RingHom.ker f) := by
    constructor
    intro q
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective q
    induction l using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq =>
      rw [map_add]
      exact (integralClosure (F s k) (L s k ⧸ RingHom.ker f)).add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      exact (integralClosure (F s k) (L s k ⧸ RingHom.ker f)).mul_mem hp (hX j)
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hfield := isField_of_isIntegral_of_isField' (R := F s k) (S := L s k ⧸ RingHom.ker f)
    (Field.toIsField _)
  exact Ideal.Quotient.maximal_of_isField _ hfield

theorem height_eq (htb : IsTranscendenceBasis k (fun i : s => x P i.1)) :
    P.height = (Fintype.card (σ s) : ℕ∞) := by
  haveI := isMax P s hs htb
  rw [← height_ker_ψL P s hs]
  let e1 : L s k ≃+* MvPolynomial (Fin (Fintype.card (σ s))) (F s k) :=
    (renameEquiv (F s k) (Fintype.equivFin (σ s))).toRingEquiv
  rw [← e1.height_map]
  haveI : ((RingHom.ker (ψL P s hs)).map e1).IsMaximal := map_isMaximal_of_equiv e1
  exact A3S51HVK.maxHeight _ (F s k) _

omit hs in
lemma card_σ : Fintype.card (σ s) + s.card = n := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have := s.card_le_univ
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

theorem height_add (htb : IsTranscendenceBasis k (fun i : s => x P i.1)) :
    P.height + s.card = n := by
  rw [height_eq P s hs htb]
  exact_mod_cast card_σ s

end A3S51HTK


namespace A3S51TBK

theorem fin {k : Type u} [Field k] {n : Nat} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    Algebra.trdeg k (FractionRing (MvPolynomial (Fin n) k ⧸ P)) < Cardinal.aleph0 := by
  classical
  set K := FractionRing (MvPolynomial (Fin n) k ⧸ P)
  set R := MvPolynomial (Fin n) k
  set A := R ⧸ P
  let x : Fin n → K := fun i => algebraMap R K (MvPolynomial.X i)
  let t : Set K := Set.range x
  -- every image of a polynomial lies in adjoin ℂ t
  have hmem : ∀ p : R, algebraMap R K p ∈ Algebra.adjoin k t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show algebraMap R K (MvPolynomial.C a) = algebraMap k K a from
        (IsScalarTower.algebraMap_apply k R K a).symm]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]; exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hA : ∀ a : A, algebraMap A K a ∈ Algebra.adjoin k t := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap A K (Ideal.Quotient.mk P p) = algebraMap R K p := by
      rw [IsScalarTower.algebraMap_apply R A K]; rfl
    rw [this]; exact hmem p
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k t) K := by
    constructor
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : algebraMap A K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    let a' : Algebra.adjoin k t := ⟨_, hA a⟩
    let b' : Algebra.adjoin k t := ⟨_, hA b⟩
    refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero] at this
      exact hb0 (congrArg Subtype.val this)
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap A K b * (algebraMap A K a / algebraMap A K b) - algebraMap A K a = 0
      rw [mul_div_cancel₀ _ hb0, sub_self]
  refine lt_of_le_of_lt (Algebra.IsAlgebraic.trdeg_le_cardinalMk k t) ?_
  exact (Set.finite_range x).lt_aleph0

theorem tb
    {k : Type u} [Field k] {n : Nat}
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    ∃ s : Finset (Fin n),
      AlgebraicIndependent k
        (fun i : s => algebraMap (MvPolynomial (Fin n) k)
          (FractionRing (MvPolynomial (Fin n) k ⧸ P)) (MvPolynomial.X i.1)) ∧
      s.card = (Algebra.trdeg k (FractionRing (MvPolynomial (Fin n) k ⧸ P))).toNat := by
  classical
  set K := FractionRing (MvPolynomial (Fin n) k ⧸ P)
  set R := MvPolynomial (Fin n) k
  set A := R ⧸ P
  let x : Fin n → K := fun i => algebraMap R K (MvPolynomial.X i)
  let t : Set K := Set.range x
  -- every image of a polynomial lies in adjoin ℂ t
  have hmem : ∀ p : R, algebraMap R K p ∈ Algebra.adjoin k t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show algebraMap R K (MvPolynomial.C a) = algebraMap k K a from
        (IsScalarTower.algebraMap_apply k R K a).symm]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]; exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hA : ∀ a : A, algebraMap A K a ∈ Algebra.adjoin k t := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap A K (Ideal.Quotient.mk P p) = algebraMap R K p := by
      rw [IsScalarTower.algebraMap_apply R A K]; rfl
    rw [this]; exact hmem p
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k t) K := by
    constructor
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : algebraMap A K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    let a' : Algebra.adjoin k t := ⟨_, hA a⟩
    let b' : Algebra.adjoin k t := ⟨_, hA b⟩
    refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero] at this
      exact hb0 (congrArg Subtype.val this)
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap A K b * (algebraMap A K a / algebraMap A K b) - algebraMap A K a = 0
      rw [mul_div_cancel₀ _ hb0, sub_self]
  obtain ⟨u, hut, hu⟩ := exists_isTranscendenceBasis_subset (R := k) t
  have hfin : u.Finite := (Set.finite_range x).subset hut
  have hpre : ∀ y : u, ∃ i, x i = y.1 := fun y => hut y.2
  let g : u → Fin n := fun y => Classical.choose (hpre y)
  have hg : ∀ y, x (g y) = y.1 := fun y => Classical.choose_spec (hpre y)
  have ginj : Function.Injective g := by
    intro y z h; apply Subtype.ext; rw [← hg y, ← hg z, h]
  haveI : Fintype u := hfin.fintype
  set S : Finset (Fin n) := Finset.univ.image g with hS
  refine ⟨S, ?_, ?_⟩
  · have hmemu : ∀ i : S, x i.1 ∈ u := by
      intro ⟨i, hi⟩
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hi)
      simpa [hg y] using y.2
    let f : S → u := fun i => ⟨x i.1, hmemu i⟩
    have finj : Function.Injective f := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ h
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hi)
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (hS ▸ hj)
      have : x (g y) = x (g z) := congrArg Subtype.val h
      rw [hg, hg] at this
      have : y = z := Subtype.ext this
      subst this; rfl
    exact hu.1.comp f finj
  · rw [hS, Finset.card_image_of_injective _ ginj, Finset.card_univ]
    have := hu.cardinalMk_eq_trdeg
    rw [← this, Cardinal.mk_fintype, Cardinal.toNat_natCast]


theorem height_add {k : Type u} [Field k] {n : Nat} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    P.height + (Algebra.trdeg k (FractionRing (MvPolynomial (Fin n) k ⧸ P))).toNat = n := by
  obtain ⟨s, hs, hcard⟩ := tb P
  have htb : IsTranscendenceBasis k
      (fun i : s => algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k ⧸ P))
        (MvPolynomial.X i.1)) := by
    apply hs.isTranscendenceBasis_of_lift_trdeg_le_of_finite
    rw [Cardinal.mk_coe_finset, ← Cardinal.cast_toNat_of_lt_aleph0 (fin P), hcard]
    simp
  rw [← hcard]
  exact A3S51HTK.height_add P s hs htb

end A3S51TBK

namespace A3S51TBK
theorem trdeg_quot {k : Type u} [Field k] {n : Nat} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P) =
      Algebra.trdeg k (FractionRing (MvPolynomial (Fin n) k ⧸ P)) := by
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin n) k ⧸ P) (FractionRing (MvPolynomial (Fin n) k ⧸ P)) :=
    IsLocalization.isAlgebraic (S := FractionRing (MvPolynomial (Fin n) k ⧸ P)) (nonZeroDivisors _)
  have h := trdeg_add_eq k (MvPolynomial (Fin n) k ⧸ P) (A := FractionRing (MvPolynomial (Fin n) k ⧸ P))
  rw [trdeg_eq_zero (R := MvPolynomial (Fin n) k ⧸ P) (A := FractionRing (MvPolynomial (Fin n) k ⧸ P)), add_zero] at h
  exact h

theorem final {k : Type u} [Field k] {n : Nat} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] :
    n <= P.height + (Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ P)).toNat := by
  rw [trdeg_quot]; exact (height_add P).ge
end A3S51TBK

theorem solution
    {K : Type*} [Field K] {n : Nat}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] :
    n ≤ P.height +
      (Algebra.trdeg K
        (FractionRing (MvPolynomial (Fin n) K ⧸ P))).toNat := by
  exact (A3S51TBK.height_add P).ge

