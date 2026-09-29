-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/aa80854f-1f47-575c-993c-f749d23d642f

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
import Theorems.Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace LBShared

open IsLocalRing NeronSpecialFibreInfra ModularCurve ModularCurve.JZeroNeronObjectAtP

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {t : ℕ}

theorem mem_valuationSubring_of_pow_eq_one (A : ValuationSubring (AlgebraicClosure ℚ)) {m : ℕ} (hm : 0 < m)
    {x : AlgebraicClosure ℚ} (hx : x ^ m = 1) : x ∈ A := by
  have hint : IsIntegral ↥A x := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hx, sub_self]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
  rw [← hy]
  exact y.2

theorem exists_isPrimitiveRoot_valuationSubring (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [NeZero ℓ] :
    ∃ ζ : ↥A, IsPrimitiveRoot ζ ℓ := by
  have hdeg : (Polynomial.cyclotomic ℓ (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos ℓ)).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot z ℓ := (Polynomial.isRoot_cyclotomic_iff).mp hz
  have hzA : z ∈ A := mem_valuationSubring_of_pow_eq_one A (NeZero.pos ℓ) hprim.pow_eq_one
  refine ⟨⟨z, hzA⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (by exact hprim) Subtype.val_injective

theorem pow_val_add {R : Type*} [Monoid R] {ℓ : ℕ} [NeZero ℓ] (a : R) (ha : a ^ ℓ = 1) (x y : ZMod ℓ) :
    a ^ (x + y).val = a ^ x.val * a ^ y.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) ℓ, pow_add, pow_mul, ha, one_pow, one_mul]

def testChar (ℓ : ℕ) [NeZero ℓ] (ζA : ↥A) (hζA : ζA ^ ℓ = 1) (i : Fin t) :
    AddMonoidAlgebra ↥A (Fin t → ZMod ℓ) →ₐ[↥A] ↥A :=
  AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod ℓ)
    { toFun := fun g => ζA ^ ((Multiplicative.toAdd g) i).val
      map_one' := by
        change ζA ^ ((0 : Fin t → ZMod ℓ) i).val = 1
        rw [Pi.zero_apply, ZMod.val_zero, pow_zero]
      map_mul' := fun g h => by
        change ζA ^ ((Multiplicative.toAdd g + Multiplicative.toAdd h) i).val =
          ζA ^ ((Multiplicative.toAdd g) i).val * ζA ^ ((Multiplicative.toAdd h) i).val
        rw [Pi.add_apply, pow_val_add ζA hζA] }

theorem testChar_single (ℓ : ℕ) [NeZero ℓ] (ζA : ↥A) (hζA : ζA ^ ℓ = 1) (i : Fin t) (g : Fin t → ZMod ℓ) :
    testChar ℓ ζA hζA i (AddMonoidAlgebra.single g 1) = ζA ^ (g i).val := by
  rw [testChar, AddMonoidAlgebra.lift_single, one_smul]
  rfl

abbrev red {t : ℕ} (ℓ : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod ℓ) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod ℓ)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem red_apply {t : ℕ} (ℓ : ℕ) (v : Fin t → ℤ) : red ℓ v = fun i => ((v i : ℤ) : ZMod ℓ) := rfl

theorem eq_of_forall_prime_pow_single_eq {p : ℕ} (hp : p.Prime) (N N' : (Fin t → ℤ) →+ (Fin t → ℤ))
    (h : ∀ (B : ℕ), ∃ (ℓ : ℕ), B ≤ ℓ ∧ ℓ.Prime ∧ ℓ ≠ p ∧
      ∃ (Nb Nb' : (Fin t → ZMod ℓ) →+ (Fin t → ZMod ℓ)),
        Nb.comp (red ℓ) = (red ℓ).comp N ∧ Nb'.comp (red ℓ) = (red ℓ).comp N' ∧
        ∀ (χ : AddMonoidAlgebra ↥A (Fin t → ZMod ℓ) →ₐ[↥A] ↥A) (g : Fin t → ZMod ℓ),
          χ (AddMonoidAlgebra.single (Nb g) 1) ^ p = χ (AddMonoidAlgebra.single (Nb' g) 1) ^ p) :
    N = N' := by
  classical
  suffices key : ∀ j i : Fin t, N (Pi.single j 1) i = N' (Pi.single j 1) i by
    refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
    have e : (Pi.single j x : Fin t → ℤ) = x • Pi.single j 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e, map_zsmul, map_zsmul]
    exact congrArg (fun u => x • u) (funext (key j))
  intro j i
  set a := N (Pi.single j 1) i with ha
  set b := N' (Pi.single j 1) i with hb
  obtain ⟨ℓ, hℓge, hℓ, hℓp, Nb, Nb', hNb, hNb', hχ⟩ := h (max p (a - b).natAbs + 1)
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓab : (a - b).natAbs < ℓ := by omega
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_valuationSubring A ℓ

  have hg : Nb (red ℓ (Pi.single j 1)) = red ℓ (N (Pi.single j 1)) := DFunLike.congr_fun hNb (Pi.single j 1)
  have hg' : Nb' (red ℓ (Pi.single j 1)) = red ℓ (N' (Pi.single j 1)) := DFunLike.congr_fun hNb' (Pi.single j 1)
  have hh := hχ (testChar ℓ ζ hζ.pow_eq_one i) (red ℓ (Pi.single j 1))
  rw [hg, hg', testChar_single, testChar_single, red_apply, red_apply, ← pow_mul, ← pow_mul] at hh

  obtain ⟨u, hu⟩ : ∃ u : (↥A)ˣ, (u : ↥A) = ζ := ⟨(hζ.isUnit hℓ.ne_zero).unit, IsUnit.unit_spec _⟩
  have huℓ : IsPrimitiveRoot u ℓ := IsPrimitiveRoot.coe_units_iff.mp (by rw [hu]; exact hζ)
  have h' : u ^ (((a : ZMod ℓ)).val * p) = u ^ (((b : ZMod ℓ)).val * p) :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]; exact hh)
  rw [pow_eq_pow_iff_modEq, ← huℓ.eq_orderOf] at h'
  have hx : ((a : ZMod ℓ)).val ≡ ((b : ZMod ℓ)).val [MOD ℓ] :=
    Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.symm ((Nat.coprime_primes hp hℓ).mpr hℓp.symm)) h'
  have hab : (a : ZMod ℓ) = (b : ZMod ℓ) :=
    ZMod.val_injective ℓ (Nat.ModEq.eq_of_lt_of_lt hx (ZMod.val_lt _) (ZMod.val_lt _))
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hab
  have h0 : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hab (by
    rw [← Int.natAbs_neg, neg_sub] at hℓab
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hℓab)
  omega

theorem forall_bound_of_forall_prime_ne {p : ℕ} {P : ℕ → Prop} (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → P ℓ) (B : ℕ) :
    ∃ ℓ, B ≤ ℓ ∧ ℓ.Prime ∧ ℓ ≠ p ∧ P ℓ := by
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (max B (p + 1))
  exact ⟨ℓ, le_trans (le_max_left _ _) hℓge, hℓ, by omega, h ℓ hℓ (by omega)⟩

theorem mapDomainAlgHom_single (k : Type*) [CommSemiring k] {G G' : Type*} [AddMonoid G] [AddMonoid G'] (f : G →+ G') (g : G) :
    AddMonoidAlgebra.mapDomainAlgHom k k f (AddMonoidAlgebra.single g (1 : k)) = AddMonoidAlgebra.single (f g) 1 := by
  change AddMonoidAlgebra.mapDomainRingHom k f (AddMonoidAlgebra.single g 1) = _
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]

theorem red_eq_red_of_sub {t : ℕ} (ℓ : ℕ) (N : (Fin t → ℤ) →+ (Fin t → ℤ)) {v w : Fin t → ℤ}
    (h : red ℓ v = red ℓ w) : red ℓ (N v) = red ℓ (N w) := by

  have hd : ∀ i, (ℓ : ℤ) ∣ (v - w) i := fun i => by
    have := congrFun h i
    change ((v i : ℤ) : ZMod ℓ) = ((w i : ℤ) : ZMod ℓ) at this
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
    rw [Pi.sub_apply, ← neg_sub]
    exact (dvd_neg).mpr this
  choose u hu using hd
  have hvw : v - w = (ℓ : ℤ) • (fun i => u i) := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, ← hu i]
  have hN : N v - N w = (ℓ : ℤ) • N (fun i => u i) := by rw [← map_sub, hvw, map_zsmul]
  have h0 : red ℓ (N v) - red ℓ (N w) = 0 := by
    rw [← map_sub, hN, map_zsmul]
    funext i
    change ((ℓ : ℤ) • red ℓ (N fun i => u i)) i = 0
    rw [Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  exact sub_eq_zero.mp h0

theorem red_lift {t : ℕ} (ℓ : ℕ) [NeZero ℓ] (g : Fin t → ZMod ℓ) : red ℓ (fun i => ((g i).cast : ℤ)) = g :=
  funext fun i => by change (((g i).cast : ℤ) : ZMod ℓ) = g i; rw [ZMod.intCast_zmod_cast]

def reduceEnd {t : ℕ} (ℓ : ℕ) [NeZero ℓ] (N : (Fin t → ℤ) →+ (Fin t → ℤ)) : (Fin t → ZMod ℓ) →+ (Fin t → ZMod ℓ) where
  toFun g := red ℓ (N (fun i => ((g i).cast : ℤ)))
  map_zero' := by
    have e : (fun i => (((0 : Fin t → ZMod ℓ) i).cast : ℤ)) = 0 := funext fun i => by rw [Pi.zero_apply, ZMod.cast_zero]; rfl
    rw [e, map_zero, map_zero]
  map_add' g g' := by
    rw [← map_add, ← map_add]
    refine red_eq_red_of_sub ℓ N ?_
    rw [map_add, red_lift, red_lift, red_lift]

theorem reduceEnd_comp_red {t : ℕ} (ℓ : ℕ) [NeZero ℓ] (N : (Fin t → ℤ) →+ (Fin t → ℤ)) :
    (reduceEnd ℓ N).comp (red ℓ) = (red ℓ).comp N :=
  AddMonoidHom.ext fun v => by
    change red ℓ (N (fun i => (((red ℓ v) i).cast : ℤ))) = red ℓ (N v)
    exact red_eq_red_of_sub ℓ N (red_lift ℓ (red ℓ v))

theorem single_nsmul_one {R : Type*} [CommSemiring R] {G : Type*} [AddMonoid G] (n : ℕ) (g : G) :
    AddMonoidAlgebra.single (n • g) (1 : R) = AddMonoidAlgebra.single g 1 ^ n := by
  rw [AddMonoidAlgebra.single_pow, one_pow]

theorem eq_of_forall_prime_charEq {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {t : ℕ}
    (N N' : (Fin t → ℤ) →+ (Fin t → ℤ))
    (h : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (Nb Nb' : (Fin t → ZMod ℓ) →+ (Fin t → ZMod ℓ)),
      Nb.comp (red ℓ) = (red ℓ).comp N → Nb'.comp (red ℓ) = (red ℓ).comp N' →
      ∀ χA : muCoord ↥A t ℓ →ₐ[↥A] ↥A,
        χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((p • AddMonoidHom.id _).comp Nb)) =
          χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((p • AddMonoidHom.id _).comp Nb'))) :
    N = N' := by
  refine eq_of_forall_prime_pow_single_eq (A := A) (Fact.out : p.Prime) N N' fun B => ?_
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (max B (p + 1))
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓp : ℓ ≠ p := by omega
  refine ⟨ℓ, le_trans (le_max_left _ _) hℓge, hℓ, hℓp, reduceEnd ℓ N, reduceEnd ℓ N', reduceEnd_comp_red ℓ N,
    reduceEnd_comp_red ℓ N', fun χ g => ?_⟩
  have e := congrArg (fun F : muCoord ↥A t ℓ →ₐ[↥A] ↥A => F (AddMonoidAlgebra.single g 1))
    (h ℓ hℓ hℓp (reduceEnd ℓ N) (reduceEnd ℓ N') (reduceEnd_comp_red ℓ N) (reduceEnd_comp_red ℓ N') χ)
  simp only [AlgHom.comp_apply, mapDomainAlgHom_single, AddMonoidHom.comp_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply, single_nsmul_one, map_pow] at e
  exact e

theorem eq_id_of_forall_prime_charEq {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {t : ℕ}
    (N : (Fin t → ℤ) →+ (Fin t → ℤ))
    (h : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (Nb : (Fin t → ZMod ℓ) →+ (Fin t → ZMod ℓ)),
      Nb.comp (red ℓ) = (red ℓ).comp N →
      ∀ χA : muCoord ↥A t ℓ →ₐ[↥A] ↥A,
        χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((p • AddMonoidHom.id _).comp Nb)) =
          χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id _))) :
    N = AddMonoidHom.id _ :=
  eq_of_forall_prime_charEq (A := A) N (AddMonoidHom.id _) fun ℓ hℓ hℓp Nb Nb' hNb hNb' χA => by
    have hid : Nb' = AddMonoidHom.id _ := by
      refine AddMonoidHom.ext fun g => ?_
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have := DFunLike.congr_fun hNb' (fun i => ((g i).cast : ℤ))
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply, red_lift] at this
      exact this
    rw [h ℓ hℓ hℓp Nb hNb χA, hid, AddMonoidHom.comp_id]

end LBShared

end

namespace LBprimeAux

section conv

variable {S : Type} [CommRing S] {L : Type} [CommRing L] [Algebra S L] {G : Type} [AddMonoid G]

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) :
    (c * c') (AddMonoidAlgebra.single v 1) =
      c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G) :
    (1 : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (n : ℕ) (v : G) :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, pow_succ, convMul_apply_single, ih]

end conv

section chars

variable {S : Type} [CommRing S] {G : Type} [AddCommMonoid G]

theorem mapDomainAlgHom_single' (N : G →+ G) (g : G) :
    AddMonoidAlgebra.mapDomainAlgHom S S N (AddMonoidAlgebra.single g (1 : S)) = AddMonoidAlgebra.single (N g) 1 := by
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]

theorem mapDomainAlgHom_comp' (N N' : G →+ G) :
    (AddMonoidAlgebra.mapDomainAlgHom S S N).comp (AddMonoidAlgebra.mapDomainAlgHom S S N') =
      AddMonoidAlgebra.mapDomainAlgHom S S (N.comp N') := by
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, mapDomainAlgHom_single', mapDomainAlgHom_single', mapDomainAlgHom_single']
  rfl

theorem convPow_ofConv_eq_comp {L : Type} [CommRing L] [Algebra S L] (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (n : ℕ) :
    (c ^ n).ofConv = c.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S (n • AddMonoidHom.id G)) := by
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  change (c ^ n) (AddMonoidAlgebra.single g 1) = _
  rw [convPow_apply_single, AlgHom.comp_apply, mapDomainAlgHom_single']
  rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
  rfl

end chars

section Avalued

variable {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem exists_algHom_valuationSubring_of_muCoord {t m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ χA : muCoord ↥A t m →ₐ[↥A] ↥A, χ = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA := by
  classical

  have hroot : ∀ g : Fin t → ZMod m, (χ (AddMonoidAlgebra.single g 1)) ^ m = 1 := by
    intro g
    rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    have hg : m • g = 0 := by
      funext i
      show m • g i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hg]
    exact map_one χ
  have hmem : ∀ g : Fin t → ZMod m, χ (AddMonoidAlgebra.single g 1) ∈ A := by
    intro g
    have hint : IsIntegral ↥A (χ (AddMonoidAlgebra.single g 1)) := by
      refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hroot g, sub_self]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
    rw [← hy]
    exact y.2

  let φ : Multiplicative (Fin t → ZMod m) →* ↥A :=
    { toFun := fun g => ⟨χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1), hmem _⟩
      map_one' := Subtype.ext (by
        show χ (AddMonoidAlgebra.single (0 : Fin t → ZMod m) 1) = 1
        exact map_one χ)
      map_mul' := fun g h => Subtype.ext (by
        show χ (AddMonoidAlgebra.single (Multiplicative.toAdd (g * h)) 1) =
          χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1) * χ (AddMonoidAlgebra.single (Multiplicative.toAdd h) 1)
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl) }
  refine ⟨AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod m) φ, ?_⟩
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem comp_ofId_injective {R : Type*} [CommRing R] [Algebra ↥A R] {f g : R →ₐ[↥A] ↥A}
    (h : (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp f = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp g) : f = g := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  exact congrArg (fun F : R →ₐ[↥A] AlgebraicClosure ℚ => F x) h

theorem twistChar_eq_comp_nsmul [Fact p.Prime] {t ℓ : ℕ} (hℓ : (ℓ : ResidueField ↥A) ≠ 0)
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
    (χA χφ : muCoord ↥A t ℓ →ₐ[↥A] ↥A)
    (hχφ : ∀ g : Fin t → ZMod ℓ,
      χφ (AddMonoidAlgebra.single g 1) = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • χA (AddMonoidAlgebra.single g 1)) :
    χφ = χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id (Fin t → ZMod ℓ))) := by
  haveI : NeZero ℓ := ⟨fun h => hℓ (by rw [h, Nat.cast_zero])⟩
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [hχφ, AlgHom.comp_apply, mapDomainAlgHom_single']
  set a : ↥A := χA (AddMonoidAlgebra.single g 1) with ha

  have hR : χA (AddMonoidAlgebra.single ((p • AddMonoidHom.id (Fin t → ZMod ℓ)) g) 1) = a ^ p := by
    rw [ha, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    rfl
  rw [hR]

  have haℓ : a ^ ℓ = 1 := by
    rw [ha, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    have h0 : ℓ • g = 0 := by
      funext i
      show ℓ • g i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [h0]
    exact map_one χA
  obtain ⟨hinj, -⟩ := ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
    (AlgebraicClosure ℚ) A ℓ hℓ
  apply hinj
  · show (MulSemiringAction.toRingHom _ ↥A (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) a) ^ ℓ = 1
    rw [← map_pow, haℓ, map_one]
  · show (a ^ p) ^ ℓ = 1
    rw [← pow_mul, mul_comm, pow_mul, haℓ, one_pow]
  · rw [IsLocalRing.ResidueField.residue_smul, hφ.smul_residue_eq, map_pow]

end Avalued

section J0

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}

theorem coe_mul_castOver (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {T : Scheme.{0}} {s s' : T ⟶ base p} (h : s = s')
    (a b : SchemeHomOver s O.g) :
    (O.L.mul s' (castOver h a) (castOver h b)).1 = (O.L.mul s a b).1 := by
  subst h
  rfl

theorem coe_pts_toricPoint (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    (O.pts (O.toricPoint m hm χ)).1 = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA := by
  simp only [JZeroNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, genOfBaseChangePt, castOver,
    RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  rfl

theorem toricPoint_injective (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    Function.Injective (O.toricPoint m hm) := by
  intro χ χ' h
  have h1 := congrArg (fun x => O.pts x) h
  simp only [JZeroNeronObjectAtP.toricPoint, Equiv.apply_symm_apply] at h1
  have h2 := (castOverEquiv Λ.hσA).injective h1
  have h3 := (RelativeGroupLaw.baseChangePointEquiv Λ.σA (barPt A)).injective h2
  have h4 := congrArg Subtype.val h3
  simp only [NeronModelInfra.schemeHomOverComp_coe] at h4
  haveI := O.toricLift_isClosedImmersion m hm
  have h5 : Spec.map (CommRingCat.ofHom χ.toRingHom) = Spec.map (CommRingCat.ofHom χ'.toRingHom) :=
    (cancel_mono (O.toricLift m hm).1).mp h4
  have h6 := congrArg CommRingCat.Hom.hom (Spec.map_injective h5)
  simp only [CommRingCat.hom_ofHom] at h6
  exact AlgHom.ext fun x => congrFun (congrArg DFunLike.coe h6) x

theorem toricPoint_convMul (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) :
    O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv := by
  apply O.pts.injective
  apply Subtype.ext
  rw [O.pts_add]
  simp only [JZeroNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, genOfBaseChangePt]
  rw [coe_mul_castOver O Λ.hσA, ← RelativeGroupLaw.baseChangePointToBase_mul, ← O.toricLift_mul m hm χ χ']
  rfl

theorem toricPoint_one (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    O.toricPoint m hm (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
  have h := toricPoint_convMul O m hm 1 1
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem nsmul_toricPoint (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (χ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) (n : ℕ) :
    n • O.toricPoint m hm χ.ofConv = O.toricPoint m hm (χ ^ n).ofConv := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, toricPoint_one]
  | succ n ih => rw [succ_nsmul, ih, pow_succ, toricPoint_convMul]

theorem pts_symm_comp_toricPoint_eq (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (φU : SchemeHomOver O.g O.g) (Mbar : (Fin O.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m))
    (hfac : ∀ θ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m θ) (O.toricLift m hm))
          (fibreRestrictAlong Λ.σA O.g O.g φU) =
        NeronModelInfra.schemeHomOverComp
          (muPt A O.toricRank m (θ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))) (O.toricLift m hm))
    (θ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (O.toricPoint m hm θ)) φU) =
      O.toricPoint m hm (θ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := by
  apply O.pts.injective
  apply Subtype.ext
  simp only [JZeroNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, NeronModelInfra.schemeHomOverComp_coe]
  show (genOfBaseChangePt Λ.hσA _).1 ≫ φU.1 = (genOfBaseChangePt Λ.hσA _).1
  rw [← hfac θ]
  simp only [genOfBaseChangePt, castOver, RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
    Category.assoc, fibreRestrictAlong_coe_comp_fst]

theorem redEnd_unique {t m : ℕ} [NeZero m] (N : (Fin t → ℤ) →+ (Fin t → ℤ)) (Nb Nb' : (Fin t → ZMod m) →+ (Fin t → ZMod m))
    (h : Nb.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)) =
      (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)).comp N)
    (h' : Nb'.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)) =
      (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)).comp N) :
    Nb = Nb' := by
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨z, hz⟩ : ∃ z : Fin t → ℤ,
      (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)) z = g :=
    ⟨fun i => ((g i).cast : ℤ), LBShared.red_lift m g⟩
  rw [← hz]
  have e1 := congrArg (fun F : (Fin t → ℤ) →+ (Fin t → ZMod m) => F z) h
  have e2 := congrArg (fun F : (Fin t → ℤ) →+ (Fin t → ZMod m) => F z) h'
  simp only [AddMonoidHom.comp_apply] at e1 e2
  rw [e1, e2]

end J0

end LBprimeAux

open LBprimeAux in
open LBprimeAux in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    [CharP (ResidueField ↥A) p]

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)))

    (P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hP₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius (ResidueField ↥A) p))) ≫ O.torusFibre.1 =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG)

    (φU : SchemeHomOver O.g O.g)
    (hφUmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φU =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φU) (NeronModelInfra.schemeHomOverComp y φU))
    (M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
      O.torusFibre.1 ≫ (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φU).1)

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)

    (hUF : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (k : ℕ) (hm : 0 < ℓ ^ k) (χ : muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ),
      O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (φ • O.toricPoint (ℓ ^ k) hm χ)) φU) = p • O.toricPoint (ℓ ^ k) hm χ)
    (hFU : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ (k : ℕ) (hm : 0 < ℓ ^ k) (χ : muCoord ↥A O.toricRank (ℓ ^ k) →ₐ[↥A] AlgebraicClosure ℚ),
      φ • O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (O.toricPoint (ℓ ^ k) hm χ)) φU) = p • O.toricPoint (ℓ ^ k) hm χ) :
    P₀.comp M₀ = AddMonoidHom.id _ ∧ M₀.comp P₀ = AddMonoidHom.id _ := by
  classical
  haveI hac : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  have H : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
      (∀ (Nb : (Fin O.toricRank → ZMod ℓ) →+ (Fin O.toricRank → ZMod ℓ)),
        Nb.comp (LBShared.red ℓ) = (LBShared.red ℓ).comp (P₀.comp M₀) →
        ∀ χA : muCoord ↥A O.toricRank ℓ →ₐ[↥A] ↥A,
          χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((p • AddMonoidHom.id _).comp Nb)) =
            χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id _))) ∧
      (∀ (Nb : (Fin O.toricRank → ZMod ℓ) →+ (Fin O.toricRank → ZMod ℓ)),
        Nb.comp (LBShared.red ℓ) = (LBShared.red ℓ).comp (M₀.comp P₀) →
        ∀ χA : muCoord ↥A O.toricRank ℓ →ₐ[↥A] ↥A,
          χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A ((p • AddMonoidHom.id _).comp Nb)) =
            χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id _))) := by
    intro ℓ hℓ hℓp
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓpos : 0 < ℓ := hℓ.pos
    have hℓκ : (ℓ : ResidueField ↥A) ≠ 0 := fun h => hℓp
      (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).mp ((CharP.cast_eq_zero_iff (ResidueField ↥A) p ℓ).mp h)).symm)

    obtain ⟨Pbar, hPbar, hLD⟩ :=
      ModularCurve.JZeroNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
        N₀ p hpN₀ A hA Λ hΛ O ΞG hΞ₁ hΞ₂ P₀ hP₀ φ hφ hφD ℓ hℓpos
    obtain ⟨Mbar, hMbar, hTM⟩ :=
      ModularCurve.JZeroNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
        N₀ p hpN₀ A hA Λ hΛ O φU hφUmul M₀ hM₀ ℓ hℓpos

    have hUF1 := (congrArg (fun n : ℕ => ∀ (hm : 0 < n) (χ : muCoord ↥A O.toricRank n →ₐ[↥A] AlgebraicClosure ℚ),
        O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (φ • O.toricPoint n hm χ)) φU) = p • O.toricPoint n hm χ)
      (pow_one ℓ)).mp (hUF ℓ hℓ hℓp 1)
    have hFU1 := (congrArg (fun n : ℕ => ∀ (hm : 0 < n) (χ : muCoord ↥A O.toricRank n →ₐ[↥A] AlgebraicClosure ℚ),
        φ • O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (O.toricPoint n hm χ)) φU) = p • O.toricPoint n hm χ)
      (pow_one ℓ)).mp (hFU ℓ hℓ hℓp 1)

    have hPM : (Pbar.comp Mbar).comp (LBShared.red ℓ) = (LBShared.red ℓ).comp (P₀.comp M₀) := by
      change (Pbar.comp Mbar).comp (LBShared.red ℓ) = ((LBShared.red ℓ).comp P₀).comp M₀
      rw [AddMonoidHom.comp_assoc, show Mbar.comp (LBShared.red ℓ) = (LBShared.red ℓ).comp M₀ from hMbar,
        ← AddMonoidHom.comp_assoc, show Pbar.comp (LBShared.red ℓ) = (LBShared.red ℓ).comp P₀ from hPbar]
    have hMP : (Mbar.comp Pbar).comp (LBShared.red ℓ) = (LBShared.red ℓ).comp (M₀.comp P₀) := by
      change (Mbar.comp Pbar).comp (LBShared.red ℓ) = ((LBShared.red ℓ).comp M₀).comp P₀
      rw [AddMonoidHom.comp_assoc, show Pbar.comp (LBShared.red ℓ) = (LBShared.red ℓ).comp P₀ from hPbar,
        ← AddMonoidHom.comp_assoc, show Mbar.comp (LBShared.red ℓ) = (LBShared.red ℓ).comp M₀ from hMbar]

    have hcomm : Mbar.comp (p • AddMonoidHom.id (Fin O.toricRank → ZMod ℓ)) = (p • AddMonoidHom.id _).comp Mbar :=
      AddMonoidHom.ext fun g => by
        show Mbar ((p • AddMonoidHom.id _) g) = (p • AddMonoidHom.id _) (Mbar g)
        rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, AddMonoidHom.id_apply, map_nsmul]
    refine ⟨fun Nb hNb χA => ?_, fun Nb hNb χA => ?_⟩
    ·
      have eNb : Nb = Pbar.comp Mbar := redEnd_unique (P₀.comp M₀) Nb _ hNb hPM
      subst eNb
      obtain ⟨χφ, hχφ, hsmul⟩ := hLD χA
      have htw : χφ = χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id _)) :=
        twistChar_eq_comp_nsmul hℓκ hφ hφD χA χφ hχφ
      have hrel := hUF1 hℓpos ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)
      rw [hsmul, pts_symm_comp_toricPoint_eq O ℓ hℓpos φU Mbar hTM,
        show (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA = (WithConv.toConv ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)).ofConv
          from rfl,
        nsmul_toricPoint, convPow_ofConv_eq_comp] at hrel
      have hinj := toricPoint_injective O ℓ hℓpos hrel
      change ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χφ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pbar))).comp
          (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar) =
        ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id _)) at hinj
      rw [htw, AlgHom.comp_assoc, AlgHom.comp_assoc, AlgHom.comp_assoc, AlgHom.comp_assoc, mapDomainAlgHom_comp',
        mapDomainAlgHom_comp'] at hinj
      exact comp_ofId_injective hinj
    ·
      have eNb : Nb = Mbar.comp Pbar := redEnd_unique (M₀.comp P₀) Nb _ hNb hMP
      subst eNb
      obtain ⟨χφ, hχφ, hsmul⟩ := hLD (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))
      have htw : χφ = (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)).comp
          (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id _)) :=
        twistChar_eq_comp_nsmul hℓκ hφ hφD _ χφ hχφ
      have hrel := hFU1 hℓpos ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)
      rw [pts_symm_comp_toricPoint_eq O ℓ hℓpos φU Mbar hTM,
        show ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar) =
          (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) from rfl,
        hsmul,
        show (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA = (WithConv.toConv ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)).ofConv
          from rfl,
        nsmul_toricPoint, convPow_ofConv_eq_comp] at hrel
      have hinj := toricPoint_injective O ℓ hℓpos hrel
      change (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χφ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pbar)) =
        ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (p • AddMonoidHom.id _)) at hinj
      rw [htw, AlgHom.comp_assoc, AlgHom.comp_assoc, AlgHom.comp_assoc, mapDomainAlgHom_comp', mapDomainAlgHom_comp',
        ← AddMonoidHom.comp_assoc, hcomm, AddMonoidHom.comp_assoc] at hinj
      exact comp_ofId_injective hinj

  exact ⟨LBShared.eq_id_of_forall_prime_charEq (A := A) (P₀.comp M₀) fun ℓ hℓ hℓp => (H ℓ hℓ hℓp).1,
    LBShared.eq_id_of_forall_prime_charEq (A := A) (M₀.comp P₀) fun ℓ hℓ hℓp => (H ℓ hℓ hℓp).2⟩

end S_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint (solution)
