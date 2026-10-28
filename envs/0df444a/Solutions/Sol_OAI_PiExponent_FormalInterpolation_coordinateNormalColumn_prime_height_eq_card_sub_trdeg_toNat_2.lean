-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_eq_card_sub_trdeg_toNat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:37:40.964555+00:00
-- url     : https://prove2.me/submissions/aef0b514-e6a2-4258-b765-a7444c806623

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.FieldTheory.FinTrdeg
import Mathlib
set_option linter.unusedSectionVars false

namespace A3S51HV
open Ideal

theorem maxHeight : ∀ (r : ℕ) (F : Type) [Field F] (M : Ideal (MvPolynomial (Fin r) F)) [M.IsMaximal],
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

end A3S51HV

namespace A3S51HT
open Ideal MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime] (s : Finset (Fin n))

abbrev R (n : ℕ) := MvPolynomial (Fin n) ℂ
abbrev K := FractionRing (R n ⧸ P)
abbrev σ := {i : Fin n // i ∉ s}
abbrev B := MvPolynomial s ℂ
abbrev T := MvPolynomial (σ s) (B s)
abbrev F := FractionRing (B s)
abbrev L := MvPolynomial (σ s) (F s)

noncomputable def eqv : Fin n ≃ σ s ⊕ s :=
  (Equiv.sumCompl (· ∈ s)).symm.trans (Equiv.sumComm _ _)

noncomputable def e0 : R n ≃ₐ[ℂ] T s :=
  (renameEquiv ℂ (eqv s)).trans (sumAlgEquiv ℂ (σ s) s)

noncomputable def x (i : Fin n) : K P := algebraMap (R n) (K P) (X i)

noncomputable def ψ : T s →+* K P := (algebraMap (R n) (K P)).comp (e0 s).symm.toRingEquiv.toRingHom

lemma e0_symm_X (j : σ s) : (e0 s).symm (X j) = X j.1 := by
  simp [e0, sumAlgEquiv_symm_X, eqv]

lemma e0_symm_CX (i : s) : (e0 s).symm (C (X i)) = X i.1 := by
  simp [e0, sumAlgEquiv_symm_C_X, eqv]

lemma e0_symm_C (b : B s) : (e0 s).symm (C b) = rename Subtype.val b := by
  have : ((e0 s).symm.toAlgHom.comp (IsScalarTower.toAlgHom ℂ (B s) (T s))) =
      rename Subtype.val := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', rename_X]
    exact e0_symm_CX s i
  exact congrArg (fun f => f b) this

lemma ψ_C (b : B s) : ψ P s (C b) = aeval (fun i : s => x P i.1) b := by
  have : (IsScalarTower.toAlgHom ℂ (R n) (K P)).comp (rename Subtype.val) =
      aeval (fun i : s => x P i.1) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x]
  change algebraMap (R n) (K P) ((e0 s).symm (C b)) = _
  rw [e0_symm_C]
  exact congrArg (fun f => f b) this

lemma ψ_X (j : σ s) : ψ P s (X j) = x P j.1 := by
  change algebraMap (R n) (K P) ((e0 s).symm (X j)) = _
  rw [e0_symm_X]; rfl

lemma algebraMap_eq_zero (r : R n) : algebraMap (R n) (K P) r = 0 ↔ r ∈ P := by
  rw [IsScalarTower.algebraMap_apply (R n) (R n ⧸ P) (K P),
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

lemma ker_ψ : RingHom.ker (ψ P s) = P.comap ((e0 s).symm.toRingEquiv : T s →+* R n) := by
  ext t
  rw [RingHom.mem_ker, Ideal.mem_comap]
  exact algebraMap_eq_zero P _

lemma height_ker_ψ : (RingHom.ker (ψ P s)).height = P.height := by
  rw [ker_ψ]
  exact RingEquiv.height_comap _ P

noncomputable abbrev Msub : Submonoid (T s) := (nonZeroDivisors (B s)).map (C (σ := σ s))

variable (hs : AlgebraicIndependent ℂ (fun i : s => x P i.1))
include hs

lemma ψ_ne (m : Msub s) : ψ P s m ≠ 0 := by
  obtain ⟨_, ⟨b, hb, rfl⟩⟩ := m
  rw [ψ_C]
  intro h
  have : b = 0 := hs.eq_zero_of_aeval_eq_zero b h
  exact nonZeroDivisors.ne_zero hb this

noncomputable def ψL : L s →+* K P :=
  IsLocalization.lift (M := Msub s) (S := L s) (g := ψ P s) fun m => (ψ_ne P s hs m).isUnit

lemma ψL_alg (t : T s) : ψL P s hs (algebraMap (T s) (L s) t) = ψ P s t :=
  IsLocalization.lift_eq _ _

lemma comap_ker_ψL : (RingHom.ker (ψL P s hs)).comap (algebraMap (T s) (L s)) = RingHom.ker (ψ P s) := by
  ext t; rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ψL_alg]

lemma height_ker_ψL : (RingHom.ker (ψL P s hs)).height = P.height := by
  haveI : (RingHom.ker (ψ P s)).IsPrime := RingHom.ker_isPrime _
  have h1 := IsLocalization.map_comap (Msub s) (L s) (RingHom.ker (ψL P s hs))
  change Ideal.map _ (Ideal.comap _ _) = _ at h1
  rw [comap_ker_ψL] at h1
  rw [← h1, IsLocalization.height_map_of_disjoint (Msub s), height_ker_ψ]
  rw [Set.disjoint_left]
  intro t ht ht'
  exact ψ_ne P s hs ⟨t, ht⟩ ht'

noncomputable def algF : Algebra (F s) (K P) :=
  ((ψL P s hs).comp (algebraMap (F s) (L s))).toAlgebra

lemma algF_B (b : B s) :
    (ψL P s hs).comp (algebraMap (F s) (L s)) (algebraMap (B s) (F s) b) =
      aeval (fun i : s => x P i.1) b := by
  rw [RingHom.comp_apply, ← ψ_C P s, ← ψL_alg P s hs]
  congr 1
  change C (algebraMap (B s) (F s) b) = MvPolynomial.map (algebraMap (B s) (F s)) (C b)
  rw [map_C]

theorem isMax (htb : IsTranscendenceBasis ℂ (fun i : s => x P i.1)) : (RingHom.ker (ψL P s hs)).IsMaximal := by
  classical
  letI := algF P s hs
  let f : L s →ₐ[F s] K P := { ψL P s hs with commutes' := fun _ => rfl }
  have hker : RingHom.ker (ψL P s hs) = RingHom.ker f := rfl
  rw [hker]
  have hinj := Ideal.kerLiftAlg_injective f
  have hX : ∀ j : σ s, IsIntegral (F s) (Ideal.Quotient.mk (RingHom.ker f) (X j)) := by
    intro j
    apply IsAlgebraic.isIntegral
    rw [← isAlgebraic_algHom_iff (Ideal.kerLiftAlg f) hinj]
    have hfx : Ideal.kerLiftAlg f (Ideal.Quotient.mk (RingHom.ker f) (X j)) = x P j.1 := by
      rw [Ideal.kerLiftAlg_mk]
      change ψL P s hs (X j) = _
      rw [← ψ_X P s j, ← ψL_alg P s hs]
      congr 1
      change X j = MvPolynomial.map (algebraMap (B s) (F s)) (X j)
      rw [map_X]
    rw [hfx]
    haveI := htb.isAlgebraic
    have ha : IsAlgebraic (Algebra.adjoin ℂ (Set.range (fun i : s => x P i.1))) (x P j.1) :=
      Algebra.IsAlgebraic.isAlgebraic _
    let g : Algebra.adjoin ℂ (Set.range (fun i : s => x P i.1)) →+* F s :=
      (algebraMap (B s) (F s)).comp (hs.repr : _ →+* B s)
    have hg : Function.Injective g :=
      (IsFractionRing.injective (B s) (F s)).comp hs.aevalEquiv.symm.injective
    have := IsAlgebraic.ringHom_of_comp_eq (f := g) (g := RingHom.id (K P)) ha hg (by
      ext a
      change (ψL P s hs).comp (algebraMap (F s) (L s)) (algebraMap (B s) (F s) (hs.repr a)) = _
      rw [algF_B, hs.aeval_repr]
      rfl)
    exact this
  have hint : Algebra.IsIntegral (F s) (L s ⧸ RingHom.ker f) := by
    constructor
    intro q
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective q
    induction l using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq =>
      rw [map_add]
      exact (integralClosure (F s) (L s ⧸ RingHom.ker f)).add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      exact (integralClosure (F s) (L s ⧸ RingHom.ker f)).mul_mem hp (hX j)
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hfield := isField_of_isIntegral_of_isField' (R := F s) (S := L s ⧸ RingHom.ker f)
    (Field.toIsField _)
  exact Ideal.Quotient.maximal_of_isField _ hfield

theorem height_eq (htb : IsTranscendenceBasis ℂ (fun i : s => x P i.1)) :
    P.height = (Fintype.card (σ s) : ℕ∞) := by
  haveI := isMax P s hs htb
  rw [← height_ker_ψL P s hs]
  let e1 : L s ≃+* MvPolynomial (Fin (Fintype.card (σ s))) (F s) :=
    (renameEquiv (F s) (Fintype.equivFin (σ s))).toRingEquiv
  rw [← e1.height_map]
  haveI : ((RingHom.ker (ψL P s hs)).map e1).IsMaximal := map_isMaximal_of_equiv e1
  exact A3S51HV.maxHeight _ (F s) _

omit hs in
lemma card_σ : Fintype.card (σ s) + s.card = n := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have := s.card_le_univ
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

theorem height_add (htb : IsTranscendenceBasis ℂ (fun i : s => x P i.1)) :
    P.height + s.card = n := by
  rw [height_eq P s hs htb]
  exact_mod_cast card_σ s

end A3S51HT

open scoped BigOperators
open scoped KaehlerDifferential
open OAI.PiExponent.FormalInterpolation

namespace A3S51G
open Algebra MvPolynomial

theorem main {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K] {ι : Type*} [Fintype ι]
    (x : ι → K) (hx : IsTranscendenceBasis k x) :
    Module.finrank K (Ω[K⁄k]) = Fintype.card ι := by
  classical
  let P := MvPolynomial ι k
  let L := FractionRing P
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  have hinj : Function.Injective (aeval x : P →ₐ[k] K) :=
    algebraicIndependent_iff_injective_aeval.1 hx.1
  let φ : L →ₐ[k] K := IsFractionRing.liftAlgHom (K := L) hinj
  letI : Algebra L K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = φ (algebraMap k L c); rw [φ.commutes]
  let Rx := Algebra.adjoin k (Set.range x)
  let e := hx.1.aevalEquiv
  letI : Algebra Rx L := ((algebraMap P L).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower Rx L K := IsScalarTower.of_algebraMap_eq fun r => by
    change (r : K) = φ (algebraMap P L (e.symm r))
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    conv_lhs => rw [← e.apply_symm_apply r]
    rfl
  haveI : Algebra.IsAlgebraic Rx K := hx.isAlgebraic
  have hRxL : Function.Injective (algebraMap Rx L) :=
    (IsFractionRing.injective P L).comp e.symm.injective
  haveI : Algebra.IsAlgebraic L K := Algebra.IsAlgebraic.extendScalars hRxL
  haveI : Algebra.IsSeparable L K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale L K := Algebra.FormallyEtale.of_isSeparable L K
  haveI : Algebra.FormallyEtale P L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k L K).finrank_eq
  have h2 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k P L).finrank_eq
  rw [← h1, Module.finrank_baseChange, ← h2, Module.finrank_baseChange,
    Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k ι)]

theorem toNat {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
    (hfin : Algebra.trdeg k K < Cardinal.aleph0) :
    Module.finrank K (Ω[K⁄k]) = (Algebra.trdeg k K).toNat := by
  classical
  obtain ⟨u, hu⟩ := exists_isTranscendenceBasis k K
  have hc := hu.cardinalMk_eq_trdeg
  have hfu : u.Finite := by
    rw [← Set.finite_coe_iff, ← Cardinal.mk_lt_aleph0_iff, hc]; exact hfin
  haveI : Fintype u := hfu.fintype
  rw [main _ hu, ← hc, Cardinal.mk_fintype, Cardinal.toNat_natCast]

end A3S51G

namespace A3S51F
theorem fin {m : Nat} (P : Ideal (MvPolynomial (Fin (Nat.succ m)) Complex)) [P.IsPrime] :
    Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) < Cardinal.aleph0 := by
  classical
  set K := logarithmicPrimeField P
  set R := MvPolynomial (Fin (m + 1)) Complex
  set A := R ⧸ P
  let x : Fin (m + 1) → K := fun i => algebraMap R K (MvPolynomial.X i)
  let t : Set K := Set.range x
  -- every image of a polynomial lies in adjoin ℂ t
  have hmem : ∀ p : R, algebraMap R K p ∈ Algebra.adjoin Complex t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show algebraMap R K (MvPolynomial.C a) = algebraMap Complex K a from
        (IsScalarTower.algebraMap_apply Complex R K a).symm]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]; exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hA : ∀ a : A, algebraMap A K a ∈ Algebra.adjoin Complex t := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap A K (Ideal.Quotient.mk P p) = algebraMap R K p := by
      rw [IsScalarTower.algebraMap_apply R A K]; rfl
    rw [this]; exact hmem p
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Complex t) K := by
    constructor
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : algebraMap A K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    let a' : Algebra.adjoin Complex t := ⟨_, hA a⟩
    let b' : Algebra.adjoin Complex t := ⟨_, hA b⟩
    refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero] at this
      exact hb0 (congrArg Subtype.val this)
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap A K b * (algebraMap A K a / algebraMap A K b) - algebraMap A K a = 0
      rw [mul_div_cancel₀ _ hb0, sub_self]
  refine lt_of_le_of_lt (Algebra.IsAlgebraic.trdeg_le_cardinalMk Complex t) ?_
  exact (Set.finite_range x).lt_aleph0
end A3S51F

namespace A3S51TB
theorem tb
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    ∃ s : Finset (Fin (m + 1)),
      AlgebraicIndependent Complex
        (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (logarithmicPrimeField P) (MvPolynomial.X i.1)) ∧
      s.card = (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by
  classical
  set K := logarithmicPrimeField P
  set R := MvPolynomial (Fin (m + 1)) Complex
  set A := R ⧸ P
  let x : Fin (m + 1) → K := fun i => algebraMap R K (MvPolynomial.X i)
  let t : Set K := Set.range x
  -- every image of a polynomial lies in adjoin ℂ t
  have hmem : ∀ p : R, algebraMap R K p ∈ Algebra.adjoin Complex t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show algebraMap R K (MvPolynomial.C a) = algebraMap Complex K a from
        (IsScalarTower.algebraMap_apply Complex R K a).symm]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]; exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hA : ∀ a : A, algebraMap A K a ∈ Algebra.adjoin Complex t := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap A K (Ideal.Quotient.mk P p) = algebraMap R K p := by
      rw [IsScalarTower.algebraMap_apply R A K]; rfl
    rw [this]; exact hmem p
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Complex t) K := by
    constructor
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : algebraMap A K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    let a' : Algebra.adjoin Complex t := ⟨_, hA a⟩
    let b' : Algebra.adjoin Complex t := ⟨_, hA b⟩
    refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero] at this
      exact hb0 (congrArg Subtype.val this)
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap A K b * (algebraMap A K a / algebraMap A K b) - algebraMap A K a = 0
      rw [mul_div_cancel₀ _ hb0, sub_self]
  obtain ⟨u, hut, hu⟩ := exists_isTranscendenceBasis_subset (R := Complex) t
  have hfin : u.Finite := (Set.finite_range x).subset hut
  have hpre : ∀ y : u, ∃ i, x i = y.1 := fun y => hut y.2
  let g : u → Fin (m + 1) := fun y => Classical.choose (hpre y)
  have hg : ∀ y, x (g y) = y.1 := fun y => Classical.choose_spec (hpre y)
  have ginj : Function.Injective g := by
    intro y z h; apply Subtype.ext; rw [← hg y, ← hg z, h]
  haveI : Fintype u := hfin.fintype
  set S : Finset (Fin (m + 1)) := Finset.univ.image g with hS
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

end A3S51TB

namespace A3S51AL

variable {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]

abbrev R (m : Nat) := MvPolynomial (Fin (m + 1)) Complex

/-- derivation on R from a vector a -/
noncomputable def D0 (a : Fin (m + 1) → logarithmicPrimeField P) :
    Derivation Complex (R m) (logarithmicPrimeField P) :=
  ∑ i, a i • (Algebra.linearMap (R m) (logarithmicPrimeField P)).compDer (MvPolynomial.pderiv i)

lemma D0_apply (a : Fin (m + 1) → logarithmicPrimeField P) (p : R m) :
    D0 P a p = ∑ i, a i * algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.pderiv i p) := by
  rw [D0, ← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
  rfl

lemma D0_X (a : Fin (m + 1) → logarithmicPrimeField P) (j : Fin (m + 1)) :
    D0 P a (MvPolynomial.X j) = a j := by
  rw [D0_apply]
  simp [MvPolynomial.pderiv_X, Pi.single_apply]


abbrev A (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) := R m ⧸ P

lemma smul_mk (p : R m) (k : logarithmicPrimeField P) :
    (Ideal.Quotient.mk P p) • k = p • k := by
  rw [← smul_one_smul (A P) p k]
  congr 1
  exact Algebra.algebraMap_eq_smul_one (A := A P) p

noncomputable def L1 (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) :
    A P →ₗ[Complex] logarithmicPrimeField P :=
  ((P.restrictScalars Complex).liftQ (D0 P a).toLinearMap (fun F hF => ha F hF)).comp
    (Submodule.Quotient.restrictScalarsEquiv Complex P).symm.toLinearMap

lemma L1_mk (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) (p : R m) :
    L1 P a ha (Ideal.Quotient.mk P p) = D0 P a p := rfl

noncomputable def D1 (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) :
    Derivation Complex (A P) (logarithmicPrimeField P) where
  toLinearMap := L1 P a ha
  map_one_eq_zero' := by
    change L1 P a ha (Ideal.Quotient.mk P 1) = 0
    rw [L1_mk, Derivation.map_one_eq_zero]
  leibniz' := by
    intro x y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    change L1 P a ha (Ideal.Quotient.mk P (p * q)) = _
    simp only [L1_mk, Derivation.leibniz, smul_mk]


instance : Algebra.FormallyEtale (A P) (logarithmicPrimeField P) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (A P))

noncomputable def phi (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0) :
    Ω[logarithmicPrimeField P⁄Complex] →ₗ[logarithmicPrimeField P] logarithmicPrimeField P :=
  (LinearMap.liftBaseChange (logarithmicPrimeField P) (D1 P a ha).liftKaehlerDifferential).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Complex (A P)
      (logarithmicPrimeField P)).symm.toLinearMap

lemma phi_X (a : Fin (m + 1) → logarithmicPrimeField P) (ha : ∀ F ∈ P, D0 P a F = 0)
    (j : Fin (m + 1)) :
    phi P a ha (KaehlerDifferential.D Complex (logarithmicPrimeField P)
      (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X j))) = a j := by
  rw [IsScalarTower.algebraMap_apply (R m) (A P) (logarithmicPrimeField P)]
  simp only [phi, LinearMap.comp_apply, LinearEquiv.coe_coe,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D, one_smul]
  exact D0_X P a j

instance : Module.Finite (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex]) :=
  Module.Finite.equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Complex (A P)
      (logarithmicPrimeField P))

theorem main :
    m + 1 ≤
      Module.finrank (logarithmicPrimeField P)
        (Submodule.span (logarithmicPrimeField P)
          (Set.range (coordinateNormalColumnAtPrime P))) +
      Module.finrank (logarithmicPrimeField P)
        (Ω[logarithmicPrimeField P⁄Complex]) := by
  classical
  set K := logarithmicPrimeField P
  let c := coordinateNormalColumnAtPrime P
  let T := Fintype.linearCombination K c
  let E : Module.Dual K (Ω[K⁄Complex]) →ₗ[K] (Fin (m + 1) → K) :=
    LinearMap.pi fun j => Module.Dual.eval K _ (KaehlerDifferential.D Complex K
      (algebraMap (R m) K (MvPolynomial.X j)))
  have hker : LinearMap.ker T ≤ LinearMap.range E := by
    intro a ha
    have ha' : ∀ F ∈ P, D0 P a F = 0 := by
      intro F hF
      have := congrFun (LinearMap.mem_ker.mp ha) ⟨F, hF⟩
      rw [Fintype.linearCombination_apply, Finset.sum_apply] at this
      rw [D0_apply]
      simpa [Pi.smul_apply, smul_eq_mul, c, coordinateNormalColumnAtPrime] using this
    refine ⟨phi P a ha', funext fun j => ?_⟩
    exact phi_X P a ha' j
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  rw [Fintype.range_linearCombination, Module.finrank_fin_fun] at h1
  have h2 := Submodule.finrank_mono hker
  have h3 := LinearMap.finrank_range_le E
  rw [Subspace.dual_finrank_eq] at h3
  have h4 : m + 1 ≤ Module.finrank K ↥(Submodule.span K (Set.range c)) +
      Module.finrank K (Ω[K⁄Complex]) := by omega
  exact h4

end A3S51AL

namespace A3S50JL

variable {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]

abbrev R (m : Nat) := MvPolynomial (Fin (m + 1)) Complex

/-- chain rule for a derivation on the function field -/
theorem deriv_formula (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P))
    (p : R m) :
    D (algebraMap (R m) (logarithmicPrimeField P) p) =
      ∑ i, algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.pderiv i p) *
        D (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.C a) =
      algebraMap Complex _ a from (IsScalarTower.algebraMap_apply Complex (R m) _ a).symm]
    simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, D.leibniz, hp]
    simp_rw [MvPolynomial.pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [smul_eq_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_eq_single j]
      · rw [MvPolynomial.pderiv_X_self, map_one, mul_one, smul_eq_mul]
      · intro i _ hij
        rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg (Ne.symm hij), map_zero, mul_zero,
          zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h

/-- derivations are determined by their values on the coordinates -/
theorem deriv_ext (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P))
    (h : ∀ i, D (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X i)) = 0) : D = 0 := by
  have hR : ∀ p : R m, D (algebraMap (R m) (logarithmicPrimeField P) p) = 0 := by
    intro p; rw [deriv_formula]; simp [h]
  have hA : ∀ a : R m ⧸ P, D (algebraMap (R m ⧸ P) (logarithmicPrimeField P) a) = 0 := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap (R m ⧸ P) (logarithmicPrimeField P) (Ideal.Quotient.mk P p) =
        algebraMap (R m) (logarithmicPrimeField P) p := by
      rw [IsScalarTower.algebraMap_apply (R m) (R m ⧸ P) (logarithmicPrimeField P)]; rfl
    rw [this, hR]
  ext z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R m ⧸ P) z
  have hb0 : algebraMap (R m ⧸ P) (logarithmicPrimeField P) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key := D.leibniz (algebraMap (R m ⧸ P) (logarithmicPrimeField P) b)
    (algebraMap _ (logarithmicPrimeField P) a / algebraMap (R m ⧸ P) (logarithmicPrimeField P) b)
  rw [mul_div_cancel₀ _ hb0, hA, hA, smul_zero, add_zero, smul_eq_mul] at key
  simpa [hb0] using key.symm

/-- the Jacobian map `a ↦ ∑ aᵢ • cᵢ` -/
noncomputable abbrev T : (Fin (m + 1) → logarithmicPrimeField P) →ₗ[logarithmicPrimeField P]
    (P → logarithmicPrimeField P) :=
  Fintype.linearCombination (logarithmicPrimeField P) (coordinateNormalColumnAtPrime P)

theorem coords_mem_ker (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)) :
    (fun i => D (algebraMap (R m) (logarithmicPrimeField P) (MvPolynomial.X i))) ∈
      LinearMap.ker (T P) := by
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
  funext F
  have hF : algebraMap (R m) (logarithmicPrimeField P) (F : R m) = 0 := by
    rw [IsScalarTower.algebraMap_apply (R m) (R m ⧸ P) (logarithmicPrimeField P)]
    show algebraMap (R m ⧸ P) (logarithmicPrimeField P) (Ideal.Quotient.mk P (F : R m)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr F.2, map_zero]
  have := deriv_formula P D F
  rw [hF, D.map_zero] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [coordinateNormalColumnAtPrime, mul_comm]

noncomputable def Phi : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)
    →ₗ[logarithmicPrimeField P] LinearMap.ker (T P) where
  toFun D := ⟨_, coords_mem_ker P D⟩
  map_add' D E := by ext; simp
  map_smul' c D := by ext; simp

theorem Phi_injective : Function.Injective (Phi P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  apply deriv_ext P D
  intro i
  have := congrFun (Subtype.ext_iff.mp hD) i
  simpa [Phi] using this

theorem le_main :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))) +
      Module.finrank (logarithmicPrimeField P)
        (Ω[logarithmicPrimeField P⁄Complex]) ≤ m + 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (T P)
  rw [Fintype.range_linearCombination] at hrn
  have hm : Module.finrank (logarithmicPrimeField P) (Fin (m + 1) → logarithmicPrimeField P) =
    m + 1 := Module.finrank_fin_fun _
  suffices Module.finrank (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex]) ≤
      Module.finrank (logarithmicPrimeField P) (LinearMap.ker (T P)) by omega
  by_cases hfin : Module.Finite (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex])
  · rw [← Subspace.dual_finrank_eq,
      (KaehlerDifferential.linearMapEquivDerivation Complex (logarithmicPrimeField P)).finrank_eq]
    exact LinearMap.finrank_le_finrank_of_injective (Phi_injective P)
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _

end A3S50JL


namespace A3S51C
open MvPolynomial

variable {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]

theorem htb_of (s : Finset (Fin (m + 1)))
    (hs : AlgebraicIndependent Complex
      (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (logarithmicPrimeField P) (MvPolynomial.X i.1)))
    (hcard : s.card = (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) :
    IsTranscendenceBasis Complex
      (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (logarithmicPrimeField P) (MvPolynomial.X i.1)) := by
  apply hs.isTranscendenceBasis_of_trdeg_le_of_finite
  rw [Cardinal.mk_coe_finset, ← Cardinal.cast_toNat_of_lt_aleph0 (A3S51F.fin P), hcard]

theorem height_add (s : Finset (Fin (m + 1)))
    (hs : AlgebraicIndependent Complex
      (fun i : s => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (logarithmicPrimeField P) (MvPolynomial.X i.1)))
    (hcard : s.card = (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) :
    P.height + s.card = m + 1 :=
  A3S51HT.height_add P s hs (htb_of P s hs hcard)

theorem height_add_trdeg :
    P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat = m + 1 := by
  obtain ⟨s, hs, hcard⟩ := A3S51TB.tb P
  rw [← hcard]
  exact height_add P s hs hcard

theorem height_toNat_add_trdeg :
    P.height.toNat + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat = m + 1 := by
  have h := height_add_trdeg P
  have hne : P.height ≠ ⊤ := by
    intro htop; rw [htop, top_add] at h; exact ENat.top_ne_natCast _ h
  have : (P.height.toNat : ℕ∞) = P.height := ENat.natCast_toNat hne
  rw [← this] at h
  exact_mod_cast h

end A3S51C

namespace A3S51C
open MvPolynomial

variable {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]

theorem height_ne_top : P.height ≠ ⊤ := by
  have h := height_add_trdeg P
  intro htop; rw [htop, top_add] at h; exact ENat.top_ne_natCast _ h

theorem span_add :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P) (Set.range (coordinateNormalColumnAtPrime P))) +
    Module.finrank (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex]) = m + 1 :=
  le_antisymm (A3S50JL.le_main P) (A3S51AL.main P)

theorem omega_eq :
    Module.finrank (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex]) =
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat :=
  A3S51G.toNat (A3S51F.fin P)

theorem span_eq_toNat :
    Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P) (Set.range (coordinateNormalColumnAtPrime P))) =
      P.height.toNat := by
  have h1 := span_add P
  have h2 := omega_eq P
  have h3 := height_toNat_add_trdeg P
  omega

theorem span_eq_height :
    (Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P) (Set.range (coordinateNormalColumnAtPrime P))) : ℕ∞) =
      P.height := by
  rw [span_eq_toNat, ENat.natCast_toNat (height_ne_top P)]

theorem card_eq_height (A : Finset (Fin (m + 1))) (hA : coordinateNormalBasisAtPrime P A) :
    (A.card : ℕ∞) = P.height := by
  rw [← span_eq_height P, ← hA.2, finrank_span_eq_card hA.1, Fintype.card_coe]

end A3S51C

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height = ↑((m + 1) -
      (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat) := by
  have h := A3S51C.height_toNat_add_trdeg P
  rw [← ENat.natCast_toNat (A3S51C.height_ne_top P)]
  congr 1
  omega

