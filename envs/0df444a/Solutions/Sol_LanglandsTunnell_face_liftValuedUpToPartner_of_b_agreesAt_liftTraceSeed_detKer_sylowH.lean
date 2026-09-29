-- Prove2me | solution 1 for LanglandsTunnell.face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/87697f19-2743-56eb-864e-8ca0b44a2a1e

import Definitions.Def_AutomorphicForm_HeckeEigensystemMap
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_LanglandsTunnell_P52Interface
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH

set_option Elab.async false

set_option autoImplicit false

section ResidueTower

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P0
p2m_open "LanglandsTunnell"

open Matrix

private abbrev M3 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

section UnitGrain

variable (g : GL (Fin 2) (ZMod 3))

private theorem val_pow_three_eq : ((g ^ 3 : GL (Fin 2) (ZMod 3)) : M3) = (g : M3) * g * g := by
  rw [Units.val_pow_eq_pow_val]
  exact (pow_succ (g : M3) 2 : (g : M3) ^ 3 = (g : M3) ^ 2 * g).trans (by rw [pow_two])

end UnitGrain

end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P0
p2m_open "LanglandsTunnell"

open Polynomial

private theorem card_le_of_forall_pow_eq {R : Type*} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ y : R, y ^ q = y) : Nat.card R ≤ q := by
  classical
  haveI := Fintype.ofFinite R
  have hdeg : (X ^ q - X : R[X]).natDegree = q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    rw [natDegree_X]
    exact hq
  have hf0 : (X ^ q - X : R[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hroots : ∀ y : R, y ∈ (X ^ q - X : R[X]).roots := fun y =>
    (mem_roots hf0).2 (by simp [h y])
  calc Nat.card R = Fintype.card R := Nat.card_eq_fintype_card
    _ ≤ (X ^ q - X : R[X]).roots.toFinset.card :=
        Finset.card_le_card fun y _ => Multiset.mem_toFinset.2 (hroots y)
    _ ≤ Multiset.card (X ^ q - X : R[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : R[X]).natDegree := card_roots' _
    _ = q := hdeg

end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P0
p2m_open "LanglandsTunnell"

section Tower

open NumberField FrobeniusDensity

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

private abbrev _root_.LanglandsTunnell.P0.fixFld (K : Subgroup (L ≃ₐ[ℚ] L)) : IntermediateField ℚ L := FixedPoints.intermediateField (↥K)

p2m_export "LanglandsTunnell.P0" "fixFld"
private theorem tower_isGaloisGroup (K : Subgroup (L ≃ₐ[ℚ] L)) : IsGaloisGroup (↥K) (𝓞 (↥(fixFld K))) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing _ _ _ (↥(fixFld K)) L

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

omit hℓ in
private theorem card_int_quot_ratPrimeIdeal : Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

private theorem finite_int_quot_ratPrimeIdeal : Finite (ℤ ⧸ ratPrimeIdeal ℓ) :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  Finite.of_equiv _ (Int.quotientSpanNatEquivZMod ℓ).toEquiv.symm

end Tower

end LanglandsTunnell.P0

end ResidueTower

section ExplicitLifts

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P0
p2m_open "LanglandsTunnell"

open FLT.ExplicitLift Matrix

private abbrev _root_.LanglandsTunnell.P0.Mat : Type := Lift48.Mat

p2m_export "LanglandsTunnell.P0" "Mat"
private abbrev _root_.LanglandsTunnell.P0.K48 : List Mat := Lift48.K48

p2m_export "LanglandsTunnell.P0" "K48"
private theorem _root_.LanglandsTunnell.P0.mem_closure_iff_mem_K48 (k : Mat) :
    k ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ↔ k ∈ K48 :=
  Lift48.mem_closure_iff_mem_K48 k

p2m_export "LanglandsTunnell.P0" "mem_closure_iff_mem_K48"
private abbrev _root_.LanglandsTunnell.P0.P16 : List Mat := Lift48.P16

p2m_export "LanglandsTunnell.P0" "P16"
end LanglandsTunnell.P0

end ExplicitLifts

section RelativeDegree

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"

open LanglandsTunnell.P0

private def _root_.LanglandsTunnell.P5.IsRelDegree {G : Type*} [Group G] (H : Subgroup G) (σ : G) (n : ℕ) : Prop :=
  0 < n ∧ σ ^ n ∈ H ∧ ∀ m : ℕ, 0 < m → m < n → σ ^ m ∉ H

p2m_export "LanglandsTunnell.P5" "IsRelDegree"
private theorem isRelDegree_one_iff {G : Type*} [Group G] (H : Subgroup G) (σ : G) :
    IsRelDegree H σ 1 ↔ σ ∈ H := by
  constructor
  · rintro ⟨-, h, -⟩
    simpa using h
  · intro h
    exact ⟨one_pos, by simpa using h, fun m hm hm1 => (by omega : False).elim⟩

section Seam

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

private def IsAttachedOverFixedField (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (H : Subgroup (L ≃ₐ[ℚ] L))
    (Φ : HeckeEigensystem (FixedPoints.intermediateField H : IntermediateField ℚ L) (ℤ√(-2)))
    (T : Finset ℕ) : Prop :=
  ∀ ℓ ∉ T, ∀ _ : ℓ.Prime, ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
    (_ : Finite (𝓞 L ⧸ Q)), Q.inertia (L ≃ₐ[ℚ] L) = ⊥ →
    ∀ n : ℕ, IsRelDegree H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) n →
    ∀ M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat),
      M.map red = ((e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ n) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) →
    ∀ w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)),
      w.asIdeal = Q.under (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) →
      Φ.a w = M.trace

end Seam

end LanglandsTunnell.P5

end RelativeDegree

section LiftExistence

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P0
p2m_open "LanglandsTunnell"

open FLT.ExplicitLift Matrix

private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

private theorem mem_map_redc_K48_of_det_ne_zero :
    ∀ m : Matrix (Fin 2) (Fin 2) (ZMod 3), m.det ≠ 0 → m ∈ K48.map (·.map redc) := by decide

end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"

open LanglandsTunnell.P0

private theorem lift_exists (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat), M.map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  have hdet0 : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨M, hM, hMg⟩ := List.mem_map.1 (mem_map_redc_K48_of_det_ne_zero _ hdet0)
  exact ⟨M, (mem_closure_iff_mem_K48 M).2 hM, by rw [map_red_eq_map_redc]; exact hMg⟩

end LanglandsTunnell.P5

end LiftExistence

section FrobeniusConjugation

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity Matrix FLT.ExplicitLift"

open LanglandsTunnell.P0

open scoped Pointwise

section FrobeniusGrain

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

omit [IsGalois ℚ L] in
private theorem inertia_smul_eq_bot (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : 𝓞 L, g • x - x ∈ τ • Q := fun x => AddSubgroup.mem_inertia.1 hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    refine AddSubgroup.mem_inertia.2 fun x => ?_
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem arithFrobAt_smul (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)]
    [Finite (𝓞 L ⧸ (τ • Q))] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q) = τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹ := by
  have h1 : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)) (τ • Q) :=
    IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)
  have h2 : IsArithFrobAt ℤ (τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹) (τ • Q) :=
    (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end FrobeniusGrain

end LanglandsTunnell.P5

end FrobeniusConjugation

section RationalPlaces

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity IsDedekindDomain Ideal.IsDedekindDomain AutomorphicForm"

section UnderRatPrime

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]

omit [IsGalois ℚ L] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)] in
open Rat.HeightOneSpectrum in
private theorem under_eq_ratPrime_of_natCast_mem {E : IntermediateField ℚ L}
    (𝔓 : HeightOneSpectrum (𝓞 ↥E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hmem : ((ℓ : ℕ) : 𝓞 ↥E) ∈ 𝔓.asIdeal) :
    𝔓.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ := by
  set v : HeightOneSpectrum (𝓞 ℚ) := 𝔓.under (𝓞 ℚ) with hv_def
  have hmem_v : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have : algebraMap (𝓞 ℚ) (𝓞 ↥E) ((ℓ : ℕ) : 𝓞 ℚ) ∈ 𝔓.asIdeal := by
      rwa [map_natCast]
    exact this
  have hdvd : natGenerator v ∣ ℓ := by
    rw [natGenerator_dvd_iff]
    have h := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem_v
    rwa [map_natCast] at h
  have heq : natGenerator v = ℓ := (Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) hℓ).mp hdvd
  have happ : primesEquiv (R := 𝓞 ℚ) v = ⟨ℓ, hℓ⟩ := Subtype.ext heq
  rw [hv_def, ratPrime, ← happ, Equiv.symm_apply_apply]

private theorem ratPrime_asIdeal (ℓ : ℕ) (hℓ : ℓ.Prime) :
    (ratPrime ⟨ℓ, hℓ⟩).asIdeal
      = (Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  simp [ratPrime, Rat.HeightOneSpectrum.primesEquiv,
    IsDedekindDomain.HeightOneSpectrum.ofPrime_asIdeal]

private theorem natCast_mem_ratPrime (ℓ : ℕ) (hℓ : ℓ.Prime) : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (ratPrime ⟨ℓ, hℓ⟩).asIdeal := by
  rw [ratPrime_asIdeal]
  have h := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm
    (Ideal.mem_span_singleton_self ((ℓ : ℕ) : ℤ))
  rwa [map_natCast] at h

omit [IsGalois ℚ L] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)] in
private theorem natCast_mem_of_under_eq_ratPrime {E : IntermediateField ℚ L}
    (𝔓 : HeightOneSpectrum (𝓞 ↥E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : 𝔓.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩) : ((ℓ : ℕ) : 𝓞 ↥E) ∈ 𝔓.asIdeal := by
  have h1 : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (𝔓.under (𝓞 ℚ)).asIdeal := by
    rw [h]
    exact natCast_mem_ratPrime ℓ hℓ
  have h2 : algebraMap (𝓞 ℚ) (𝓞 ↥E) ((ℓ : ℕ) : 𝓞 ℚ) ∈ 𝔓.asIdeal := h1
  rwa [map_natCast] at h2

private theorem card_quot_ratPrime (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card (𝓞 ℚ ⧸ (ratPrime ⟨ℓ, hℓ⟩).asIdeal) = ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  rw [ratPrime_asIdeal ℓ hℓ]
  have hequiv := Ideal.quotientEquiv (Ideal.span {((ℓ : ℕ) : ℤ)})
    ((Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm)
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm rfl
  rw [← Nat.card_congr hequiv.toEquiv]
  exact LanglandsTunnell.P0.card_int_quot_ratPrimeIdeal

end UnderRatPrime

end LanglandsTunnell.P5

end RationalPlaces

section TwistWeight

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P5
namespace TwistTransport
p2m_open "LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain AutomorphicForm Matrix Ideal NumberField.Ideal"

open FLT.ExplicitLift LanglandsTunnell.Lift48 FrobeniusDensity

open scoped MatrixGroups

attribute [local instance 1001] NumberField.RingOfIntegers.instMulSemiringAction

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Chi

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

private theorem zmod3_natCast_cases (ℓ : ℕ) (hℓ : ℓ.Prime) (h3 : ℓ ≠ 3) :
    (ℓ % 3 = 1 ∧ (ℓ : ZMod 3) = 1) ∨ (ℓ % 3 = 2 ∧ (ℓ : ZMod 3) = -1) := by
  have hmod : (ℓ : ZMod 3) = ((ℓ % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod ℓ 3).symm
  have hlt : ℓ % 3 < 3 := Nat.mod_lt ℓ (by norm_num)
  have hne : ℓ % 3 ≠ 0 := by
    intro h0
    have h3dvd : 3 ∣ ℓ := Nat.dvd_of_mod_eq_zero h0
    exact h3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hℓ).1 h3dvd).symm
  interval_cases h : ℓ % 3
  · exact absurd rfl hne
  · exact Or.inl ⟨rfl, by rw [hmod]; decide⟩
  · exact Or.inr ⟨rfl, by rw [hmod]; decide⟩

private theorem chiNegThreeWeight_ratPrime (ℓ : ℕ) (hℓ : ℓ.Prime) :
    LanglandsTunnell.chiNegThreeWeight (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) = ((EisensteinWeightOne.chiNegThree ℓ : ℤ) : ℤ√(-2)) := by
  show ((EisensteinWeightOne.chiNegThree ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, hℓ⟩) : ℕ) : ℤ) : ℤ√(-2)) = _
  rw [Equiv.apply_symm_apply]

end Chi

end LanglandsTunnell.P5.TwistTransport

end TwistWeight

section SeedValues

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P2
p2m_export "LanglandsTunnell.P2" "exists_pos_pow_mem relDeg primeOver under_primeOver seedFrob liftOf liftTraceSeed"
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift AutomorphicForm"

open LanglandsTunnell.P0 LanglandsTunnell.P5

open scoped Pointwise

section RelDeg

variable {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G)

omit [Finite G] in
private theorem IsRelDegree.unique {n m : ℕ} (hn : IsRelDegree H σ n) (hm : IsRelDegree H σ m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (hm.2.2 n hn.1 h hn.2.1).elim
  · exact h
  · exact (hn.2.2 m hm.1 h hm.2.1).elim

omit [Finite G] in
private theorem IsRelDegree.conj_iff {τ : G} (hτ : τ ∈ H) (n : ℕ) :
    IsRelDegree H (τ * σ * τ⁻¹) n ↔ IsRelDegree H σ n := by
  have key : ∀ k : ℕ, (τ * σ * τ⁻¹) ^ k ∈ H ↔ σ ^ k ∈ H := fun k => by
    rw [conj_pow]
    constructor
    · intro h
      have := H.mul_mem (H.mul_mem (H.inv_mem hτ) h) hτ
      simpa [mul_assoc] using this
    · intro h
      exact H.mul_mem (H.mul_mem hτ h) (H.inv_mem hτ)
  simp only [IsRelDegree, key]

open Classical in
private theorem isRelDegree_relDeg : IsRelDegree H σ (relDeg H σ) := by
  refine ⟨(Nat.find_spec (exists_pos_pow_mem H σ)).1, (Nat.find_spec (exists_pos_pow_mem H σ)).2, fun m hm hlt h => ?_⟩
  exact Nat.find_min (exists_pos_pow_mem H σ) hlt ⟨hm, h⟩

end RelDeg

section GalInt

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup (L ≃ₐ[ℚ] L))
  (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)))

private scoped instance isGaloisGroup_ringOfIntegers :
    IsGaloisGroup H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L)
    (FixedPoints.intermediateField H : IntermediateField ℚ L) L

end GalInt

section Seed

private theorem liftOf_spec (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    liftOf g ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ∧
      (liftOf g).map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Classical.epsilon_spec (p := fun M : Mat =>
    M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ∧ M.map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)))
    (lift_exists g)

private theorem liftOf_mem (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    liftOf g ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) := (liftOf_spec g).1

private theorem liftOf_red (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (liftOf g).map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := (liftOf_spec g).2

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L))

private theorem liftTraceSeed_a (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) :
    (liftTraceSeed e H).a w = (liftOf (e (seedFrob H w))).trace := rfl

end Seed

end LanglandsTunnell.P2
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

end SeedValues
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

section FrobeniusDichotomy

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"

p2m_open "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section MatrixGrain

private def redP16 : List M₃ := P16.map fun M => M.map redc

private def cyc : M₃ := !![1, 1; 0, 1]

private def cyc' : M₃ := !![1, 2; 0, 1]

private theorem cyc_mul_cyc' : cyc * cyc' = 1 := by decide

private theorem cyc'_mul_cyc : cyc' * cyc = 1 := by decide

set_option synthInstance.maxSize 1024 in
private theorem cube_mem_redP16_of_faces : ∀ A : M₃, A.det ≠ 0 →
    A ∉ redP16 → cyc * A * cyc' ∉ redP16 → cyc' * A * cyc ∉ redP16 →
    A * A * A ∈ redP16 ∧ A * A ∉ redP16 := by
  decide

end MatrixGrain
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

section FrobPower

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

private theorem mk_pow_smul_of_isArithFrobAt {σ : G} {Q : Ideal B} (hF : IsArithFrobAt A σ Q)
    (n : ℕ) (x : B) :
    Ideal.Quotient.mk Q (σ ^ n • x)
      = Ideal.Quotient.mk Q x ^ (Nat.card (A ⧸ Q.under A) ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hx : Ideal.Quotient.mk Q (σ • x)
        = Ideal.Quotient.mk Q x ^ Nat.card (A ⧸ Q.under A) := by
      rw [← map_pow, Ideal.Quotient.eq]
      exact hF x
    rw [pow_succ, mul_smul, ih (σ • x), hx, ← pow_mul, pow_succ']

variable [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_card_pow_eq_self_of_pow_mem {H : Subgroup G} [SMulCommClass (↥H) C B]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {n : ℕ}
    (hmem : arithFrobAt A G Q ^ n ∈ H) (y : C ⧸ Q.under C) :
    y ^ (Nat.card (A ⧸ Q.under A) ^ n) = y := by
  have hF : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hfix : (arithFrobAt A G Q ^ n) • algebraMap C B c = algebraMap C B c := by
    have h : (⟨arithFrobAt A G Q ^ n, hmem⟩ : ↥H) • algebraMap C B c = algebraMap C B c := by
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    exact h
  have hq := mk_pow_smul_of_isArithFrobAt hF n (algebraMap C B c)
  rw [hfix] at hq
  rw [← map_pow, Ideal.Quotient.eq, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow,
    ← Ideal.Quotient.eq, map_pow]
  exact hq.symm

end FrobPower
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

section GaloisGrain

variable {L : Type} [Field L] [NumberField L]

private def cycU : GL (Fin 2) (ZMod 3) := ⟨cyc, cyc', cyc_mul_cyc', cyc'_mul_cyc⟩

@[scoped simp] private theorem val_cycU : ((cycU : GL (Fin 2) (ZMod 3)) : M₃) = cyc := rfl

@[scoped simp] private theorem val_cycU_inv : ((cycU⁻¹ : GL (Fin 2) (ZMod 3)) : M₃) = cyc' := rfl

private theorem mem_sylowH_iff_mem_redP16 (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (γ : L ≃ₐ[ℚ] L) :
    γ ∈ LanglandsTunnell.sylowH e ↔ ((e γ : GL (Fin 2) (ZMod 3)) : M₃) ∈ redP16 := by
  rw [LanglandsTunnell.mem_sylowH_iff, redP16, List.mem_map]
  constructor
  · rintro ⟨M, hM, h⟩
    exact ⟨M, hM, by rw [← map_red_eq_map_redc]; exact h⟩
  · rintro ⟨M, hM, h⟩
    exact ⟨M, hM, by rw [map_red_eq_map_redc]; exact h⟩

private theorem exists_conj_mem_sylowH_or_isRelDegree_three
    (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (σ : L ≃ₐ[ℚ] L) :
    (∃ τ : L ≃ₐ[ℚ] L, τ * σ * τ⁻¹ ∈ LanglandsTunnell.sylowH e) ∨ IsRelDegree (LanglandsTunnell.sylowH e) σ 3 := by
  classical
  by_cases h1 : σ ∈ LanglandsTunnell.sylowH e
  · exact Or.inl ⟨1, by simpa using h1⟩
  by_cases h2 : e.symm cycU * σ * (e.symm cycU)⁻¹ ∈ LanglandsTunnell.sylowH e
  · exact Or.inl ⟨_, h2⟩
  by_cases h3 : (e.symm cycU)⁻¹ * σ * (e.symm cycU)⁻¹⁻¹ ∈ LanglandsTunnell.sylowH e
  · exact Or.inl ⟨_, h3⟩
  right
  rw [mem_sylowH_iff_mem_redP16] at h1 h2 h3
  simp only [map_mul, map_inv, inv_inv, MulEquiv.apply_symm_apply, Units.val_mul, val_cycU,
    val_cycU_inv] at h2 h3
  have hdet0 : ((e σ : GL (Fin 2) (ZMod 3)) : M₃).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨hcube, hsq⟩ := cube_mem_redP16_of_faces _ hdet0 h1 h2 h3
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [mem_sylowH_iff_mem_redP16, map_pow, LanglandsTunnell.P0.val_pow_three_eq]
    exact hcube
  · intro m hm0 hm3 hmem
    interval_cases m
    · rw [pow_one, mem_sylowH_iff_mem_redP16] at hmem
      exact h1 hmem
    · rw [mem_sylowH_iff_mem_redP16, map_pow, Units.val_pow_eq_pow_val, sq] at hmem
      exact hsq hmem

end GaloisGrain
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

end FrobeniusDichotomy
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section InertiaDegree

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"

p2m_open "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section RelDeg

variable {G : Type*} [Group G] [Finite G]

private theorem relDeg_pos (H : Subgroup G) (σ : G) : 0 < relDeg H σ := (isRelDegree_relDeg H σ).1

private theorem relDeg_dvd_of_pow_mem (H : Subgroup G) (σ : G) {m : ℕ} (hm : σ ^ m ∈ H) : relDeg H σ ∣ m := by
  have hn := isRelDegree_relDeg H σ
  by_contra hndvd
  have hpos : 0 < m % relDeg H σ :=
    Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
  have hlt : m % relDeg H σ < relDeg H σ := Nat.mod_lt _ hn.1
  refine hn.2.2 _ hpos hlt ?_
  have h := Nat.div_add_mod m (relDeg H σ)
  have hrew : σ ^ (m % relDeg H σ) = ((σ ^ relDeg H σ) ^ (m / relDeg H σ))⁻¹ * σ ^ m := by
    rw [← pow_mul, eq_inv_mul_iff_mul_eq, ← pow_add, h]
  rw [hrew]
  exact H.mul_mem (H.inv_mem (H.pow_mem hn.2.1 _)) hm

end RelDeg
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section LiftDet

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  {e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)} {H : Subgroup (L ≃ₐ[ℚ] L)}

private theorem liftTraceSeed_b (w : HeightOneSpectrum (𝓞 (↥(LanglandsTunnell.P0.fixFld H)))) :
    (liftTraceSeed e H).b w = (liftOf (e (seedFrob H w))).det := rfl

end LiftDet
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section PowMem

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_arithFrobAt_mem_of_card_under_eq_pow {H : Subgroup G}
    [SMulCommClass (↥H) C B] [Algebra.IsInvariant C B (↥H)]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {f : ℕ}
    (hcard : Nat.card (C ⧸ Q.under C) = Nat.card (A ⧸ Q.under A) ^ f)
    (hin : Q.inertia G = ⊥) : arithFrobAt A G Q ^ f ∈ H := by
  obtain ⟨s, hs⟩ := IsArithFrobAt.exists_of_isInvariant C (↥H) Q
  have hτ : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  have key : ∀ x : B, (arithFrobAt A G Q ^ f) • x - (s : G) • x ∈ Q := by
    intro x
    have h1 := mk_pow_smul_of_isArithFrobAt hτ f x
    have h2 : (s : G) • x - x ^ (Nat.card (A ⧸ Q.under A) ^ f) ∈ Q := by
      have h := hs x
      rwa [hcard] at h
    rw [← Ideal.Quotient.eq, map_pow] at h2
    rw [← Ideal.Quotient.eq, h1, h2]
  have hmem : arithFrobAt A G Q ^ f * (s : G)⁻¹ ∈ Q.inertia G := by
    intro x
    have h := key ((s : G)⁻¹ • x)
    rwa [smul_inv_smul, ← mul_smul] at h
  rw [hin, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  rw [hmem]
  exact s.2

end PowMem
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section ResidueDegree

variable {L : Type} [Field L] [NumberField L]

private theorem natCast_mem_under' (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [hQl : Q.LiesOver (ratPrimeIdeal ℓ)] :
    ((ℓ : ℕ) : 𝓞 (↥(LanglandsTunnell.P0.fixFld H))) ∈ Q.under (𝓞 (↥(LanglandsTunnell.P0.fixFld H))) := by
  have h1 : ((ℓ : ℕ) : ℤ) ∈ ratPrimeIdeal ℓ := Ideal.mem_span_singleton_self _
  rw [hQl.over] at h1
  have h2 : algebraMap ℤ (𝓞 L) ((ℓ : ℕ) : ℤ) ∈ Q := Ideal.mem_comap.mp h1
  rw [Ideal.mem_comap, map_natCast]
  simpa using h2

variable [IsGalois ℚ L]

private theorem inertiaDeg_eq_relDeg (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (w : HeightOneSpectrum (𝓞 (↥(LanglandsTunnell.P0.fixFld H)))) (hw : w.asIdeal = Q.under (𝓞 (↥(LanglandsTunnell.P0.fixFld H)))) :
    (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹_› (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  haveI hZmax : (Q.under ℤ).IsMaximal := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; infer_instance
  haveI hZfin : Finite (ℤ ⧸ Q.under ℤ) := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact finite_int_quot_ratPrimeIdeal
  haveI : Fintype (ℤ ⧸ Q.under ℤ) := Fintype.ofFinite _
  haveI hGG := tower_isGaloisGroup (L := L) H
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  have hcardZ : Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact card_int_quot_ratPrimeIdeal
  haveI hkfin : Finite ((𝓞 (↥(LanglandsTunnell.P0.fixFld H))) ⧸ w.asIdeal) := by
    rw [hw]
    exact Finite.of_injective _
      (Ideal.quotientMap_injective (I := Q) (f := algebraMap (𝓞 (↥(LanglandsTunnell.P0.fixFld H))) (𝓞 L)))
  haveI : Fintype ((𝓞 (↥(LanglandsTunnell.P0.fixFld H))) ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI hkmax : w.asIdeal.IsMaximal := w.isMaximal
  have hunder : w.under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ :=
    under_eq_ratPrime_of_natCast_mem w hℓ (by rw [hw]; exact natCast_mem_under' H Q)
  have hcb : Nat.card (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) = ℓ := by
    rw [hunder]; exact card_quot_ratPrime ℓ hℓ
  haveI : (w.under (𝓞 ℚ)).asIdeal.IsMaximal := (w.under (𝓞 ℚ)).isMaximal
  haveI hoverP : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  have hcardf : Nat.card ((𝓞 (↥(LanglandsTunnell.P0.fixFld H))) ⧸ w.asIdeal)
      = ℓ ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
    letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
    rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal), hcb]
  have hℓ1 : 1 < ℓ := hℓ.one_lt
  have hle : (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal ≤ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
    letI := Ideal.Quotient.field w.asIdeal
    have hpow : ∀ y : (𝓞 (↥(LanglandsTunnell.P0.fixFld H))) ⧸ w.asIdeal,
        y ^ (ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) = y := by
      rw [hw]
      intro y
      have h := pow_card_pow_eq_self_of_pow_mem (A := ℤ) (C := 𝓞 (↥(LanglandsTunnell.P0.fixFld H))) (H := H) Q
        (isRelDegree_relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).2.1 y
      rwa [hcardZ] at h
    have h1lt : 1 < ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := Nat.one_lt_pow (relDeg_pos H _).ne' hℓ1
    have hcle := card_le_of_forall_pow_eq h1lt hpow
    rw [hcardf] at hcle
    exact (Nat.pow_le_pow_iff_right hℓ1).mp hcle
  have hge : relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) ≤ (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal := by
    have hcard' : Nat.card ((𝓞 (↥(LanglandsTunnell.P0.fixFld H))) ⧸ Q.under (𝓞 (↥(LanglandsTunnell.P0.fixFld H))))
        = Nat.card (ℤ ⧸ Q.under ℤ) ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
      rw [hcardZ, ← hw, hcardf]
    have hmem := pow_arithFrobAt_mem_of_card_under_eq_pow (A := ℤ) (C := 𝓞 (↥(LanglandsTunnell.P0.fixFld H))) (H := H) Q hcard' hI
    have hdvd := relDeg_dvd_of_pow_mem H _ hmem
    exact Nat.le_of_dvd (Ideal.inertiaDeg'_pos (w.under (𝓞 ℚ)).asIdeal w.asIdeal) hdvd
  exact le_antisymm hle hge

end ResidueDegree
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

end InertiaDegree
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section LiftUniqueness

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"

p2m_open "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section K48

private theorem nodup_map_redc_K48 : (Lift48.K48.map fun k => k.map redc).Nodup := by decide

private theorem lift_unique_K48 {M N : Mat} (hM : M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat))
    (hN : N ∈ Submonoid.closure ({Slift, Tlift} : Set Mat)) (h : M.map red = N.map red) : M = N :=
  List.inj_on_of_nodup_map nodup_map_redc_K48 ((Lift48.mem_closure_iff_mem_K48 M).1 hM)
    ((Lift48.mem_closure_iff_mem_K48 N).1 hN)
    (by rwa [map_red_eq_map_redc, map_red_eq_map_redc] at h)

end K48
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section LiftOf

private theorem liftOf_mul (g h : GL (Fin 2) (ZMod 3)) : liftOf (g * h) = liftOf g * liftOf h :=
  lift_unique_K48 (liftOf_mem _) (Submonoid.mul_mem _ (liftOf_mem _) (liftOf_mem _))
    (by rw [Matrix.map_mul, liftOf_red, liftOf_red, liftOf_red, Units.val_mul])

private theorem liftOf_one : liftOf (1 : GL (Fin 2) (ZMod 3)) = 1 :=
  lift_unique_K48 (liftOf_mem _) (Submonoid.one_mem _)
    (by rw [liftOf_red, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)])

private theorem liftOf_inv_mul (g : GL (Fin 2) (ZMod 3)) : liftOf g⁻¹ * liftOf g = 1 := by
  rw [← liftOf_mul, inv_mul_cancel, liftOf_one]

private theorem liftOf_mul_inv (g : GL (Fin 2) (ZMod 3)) : liftOf g * liftOf g⁻¹ = 1 := by
  rw [← liftOf_mul, mul_inv_cancel, liftOf_one]

private theorem trace_liftOf_conj (g h : GL (Fin 2) (ZMod 3)) : (liftOf (g * h * g⁻¹)).trace = (liftOf h).trace := by
  rw [liftOf_mul, liftOf_mul, Matrix.trace_mul_cycle, liftOf_inv_mul, one_mul]

private theorem det_liftOf_conj (g h : GL (Fin 2) (ZMod 3)) : (liftOf (g * h * g⁻¹)).det = (liftOf h).det := by
  rw [liftOf_mul, liftOf_mul, det_mul, det_mul, mul_right_comm, ← det_mul, liftOf_mul_inv, det_one, one_mul]

end LiftOf
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section GuardFree

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

private theorem isAttachedOverFixedField_liftTraceSeed' (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L))
    (T : Finset ℕ) : IsAttachedOverFixedField e H (liftTraceSeed e H) T := by
  intro ℓ hℓT hℓ Q hQ hQℓ hfin hI n hn M hM hred w hw
  haveI : Q.LiesOver w.asIdeal := ⟨hw⟩
  haveI : (primeOver H w).LiesOver w.asIdeal := ⟨(under_primeOver H w).symm⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup w.asIdeal (primeOver H w) Q H
  have hτ' : ((τ : L ≃ₐ[ℚ] L)) • primeOver H w = Q := hτ
  subst hτ'
  have hI₀ : (primeOver H w).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
    have h := inertia_smul_eq_bot ((τ : L ≃ₐ[ℚ] L))⁻¹ (((τ : L ≃ₐ[ℚ] L)) • primeOver H w) hI
    rwa [inv_smul_smul] at h
  have hF := arithFrobAt_smul (τ : L ≃ₐ[ℚ] L) (primeOver H w) hI₀
  have hn₀ : n = relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)) := by
    rw [hF, IsRelDegree.conj_iff H _ τ.2] at hn
    exact IsRelDegree.unique H _ hn (isRelDegree_relDeg H _)
  have hpow : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (((τ : L ≃ₐ[ℚ] L)) • primeOver H w) ^ n
      = (τ : L ≃ₐ[ℚ] L) * seedFrob H w * (τ : L ≃ₐ[ℚ] L)⁻¹ := by
    rw [hF, conj_pow, seedFrob, ← hn₀]
  have hMM : M = liftOf (e ((τ : L ≃ₐ[ℚ] L) * seedFrob H w * (τ : L ≃ₐ[ℚ] L)⁻¹)) :=
    lift_unique_K48 hM (liftOf_mem _) (by rw [hred, liftOf_red, hpow])
  rw [liftTraceSeed_a, hMM, map_mul, map_mul, map_inv, trace_liftOf_conj]

private theorem seed_b_eq_det' (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (n : ℕ) (hn : IsRelDegree H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) n)
    (M : Mat) (hM : M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat))
    (hred : M.map red = ((e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ n) : GL (Fin 2) (ZMod 3)) : M₃))
    (w : HeightOneSpectrum (𝓞 (↥(LanglandsTunnell.P0.fixFld H)))) (hw : w.asIdeal = Q.under (𝓞 (↥(LanglandsTunnell.P0.fixFld H)))) :
    (liftTraceSeed e H).b w = M.det := by
  have _ := hℓ
  haveI : Q.LiesOver w.asIdeal := ⟨hw⟩
  haveI : (primeOver H w).LiesOver w.asIdeal := ⟨(under_primeOver H w).symm⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup w.asIdeal (primeOver H w) Q H
  have hτ' : ((τ : L ≃ₐ[ℚ] L)) • primeOver H w = Q := hτ
  subst hτ'
  have hI₀ : (primeOver H w).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
    have h := inertia_smul_eq_bot ((τ : L ≃ₐ[ℚ] L))⁻¹ (((τ : L ≃ₐ[ℚ] L)) • primeOver H w) hI
    rwa [inv_smul_smul] at h
  have hF := arithFrobAt_smul (τ : L ≃ₐ[ℚ] L) (primeOver H w) hI₀
  have hn₀ : n = relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)) := by
    rw [hF, IsRelDegree.conj_iff H _ τ.2] at hn
    exact IsRelDegree.unique H _ hn (isRelDegree_relDeg H _)
  have hpow : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (((τ : L ≃ₐ[ℚ] L)) • primeOver H w) ^ n
      = (τ : L ≃ₐ[ℚ] L) * seedFrob H w * (τ : L ≃ₐ[ℚ] L)⁻¹ := by
    rw [hF, conj_pow, seedFrob, ← hn₀]
  have hMM : M = liftOf (e ((τ : L ≃ₐ[ℚ] L) * seedFrob H w * (τ : L ≃ₐ[ℚ] L)⁻¹)) :=
    lift_unique_K48 hM (liftOf_mem _) (by rw [hred, liftOf_red, hpow])
  rw [liftTraceSeed_b, hMM, map_mul, map_mul, map_inv, det_liftOf_conj]

end GuardFree
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

end LiftUniqueness
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

section PlaceUnder

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"

p2m_open "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2"

open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section Generic

variable {L : Type} [Field L] [NumberField L]

private theorem natCast_mem_under_intermediateField (E : IntermediateField ℚ L) {ℓ : ℕ} (Q : Ideal (𝓞 L))
    [hQl : Q.LiesOver (ratPrimeIdeal ℓ)] : ((ℓ : ℕ) : 𝓞 ↥E) ∈ Q.under (𝓞 ↥E) := by
  have h1 : ((ℓ : ℕ) : ℤ) ∈ ratPrimeIdeal ℓ := Ideal.mem_span_singleton_self _
  rw [hQl.over] at h1
  have h2 : algebraMap ℤ (𝓞 L) ((ℓ : ℕ) : ℤ) ∈ Q := Ideal.mem_comap.mp h1
  rw [Ideal.mem_comap, map_natCast]
  simpa using h2

private noncomputable def placeUnderH (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] : HeightOneSpectrum (𝓞 (↥(LanglandsTunnell.P0.fixFld H))) :=
  ⟨Q.under _, Ideal.IsPrime.under _ Q, fun hbot => by
    have h := natCast_mem_under_intermediateField (LanglandsTunnell.P0.fixFld H) (ℓ := ℓ) Q
    rw [hbot, Ideal.mem_bot] at h
    exact hℓ.ne_zero (by exact_mod_cast h)⟩

private theorem placeUnderH_asIdeal (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] : (placeUnderH H hℓ Q).asIdeal = Q.under (𝓞 (↥(LanglandsTunnell.P0.fixFld H))) := rfl

private theorem placeUnderH_under (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] : (placeUnderH H hℓ Q).under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ :=
  under_eq_ratPrime_of_natCast_mem _ hℓ (natCast_mem_under_intermediateField (LanglandsTunnell.P0.fixFld H) (ℓ := ℓ) Q)

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

end PlaceUnder
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff sylowH mem_sylowH_iff Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.P16 P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed chiNegThreeWeight"
namespace ReadoffSol
p2m_open "LanglandsTunnell"

open NumberField IsDedekindDomain AutomorphicForm
open FrobeniusDensity
open scoped Pointwise

set_option synthInstance.maxSize 1024 in

private theorem det_eq_one_of_cube_mem_redP16 : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3),
    A * A * A ∈ LanglandsTunnell.P4.redP16 → A ∉ LanglandsTunnell.P4.redP16 → A.det = 1 := by
  decide +kernel

private theorem entries_of_mem_K48_of_cube_mem_redP16 : ∀ k ∈ LanglandsTunnell.P0.K48,
    k.map LanglandsTunnell.P0.redc * k.map LanglandsTunnell.P0.redc * k.map LanglandsTunnell.P0.redc ∈
        LanglandsTunnell.P4.redP16 →
      k.map LanglandsTunnell.P0.redc ∉ LanglandsTunnell.P4.redP16 →
      k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 ∧ (k 0 0 + k 1 1) * (k 0 0 + k 1 1) = 1 := by
  decide +kernel

private theorem pow_eight_eq_one_of_mem_redP16 : ∀ B ∈ LanglandsTunnell.P4.redP16,
    B * B * B * B * B * B * B * B = 1 := by
  decide +kernel

private theorem trace_cube_fin_two {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    (A * A * A).trace = A.trace ^ 3 - 3 * A.det * A.trace := by
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem eq_or_eq_of_satakePow_three (a s : ℂ) (hs : s * s = 1) (h : satakePow 3 a 1 = -2 * s) :
    a = s ∨ a = -2 * s := by
  have h3 : satakePow 3 a 1 = a * (a * a - 1 * 2) - 1 * a := rfl
  rw [h3] at h
  have key : (a - s) ^ 2 * (a + 2 * s) = 0 := by linear_combination h + (2 * s - 3 * a) * hs
  rcases mul_eq_zero.1 key with h0 | h0
  · exact Or.inl (sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))
  · exact Or.inr (by linear_combination h0)

private theorem chiNegThreeWeight_sq_eq_one {ℓ : ℕ} (hℓ : ℓ.Prime) (h3 : ℓ ≠ 3) :
    chiNegThreeWeight (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) ^ 2 = 1 := by
  rw [P5.TwistTransport.chiNegThreeWeight_ratPrime]
  rcases P5.TwistTransport.zmod3_natCast_cases ℓ hℓ h3 with ⟨hm, -⟩ | ⟨hm, -⟩ <;>
    norm_num [EisensteinWeightOne.chiNegThree, hm]

variable {L : Type} [Field L] [NumberField L]

private theorem cube_mem_redP16_and_notMem_of_isRelDegree_three
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (σ : L ≃ₐ[ℚ] L)
    (h : LanglandsTunnell.P5.IsRelDegree (LanglandsTunnell.sylowH e) σ 3) :
    ((e σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((e σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((e σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈
        LanglandsTunnell.P4.redP16 ∧
      ((e σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∉
        LanglandsTunnell.P4.redP16 := by
  have h3 : σ ^ 3 ∈ LanglandsTunnell.sylowH e := h.2.1
  have h1 : σ ∉ LanglandsTunnell.sylowH e := by
    have := h.2.2 1 one_pos (by norm_num)
    rwa [pow_one] at this
  rw [LanglandsTunnell.P4.mem_sylowH_iff_mem_redP16, map_pow, Units.val_pow_eq_pow_val, pow_succ, pow_two] at h3
  rw [LanglandsTunnell.P4.mem_sylowH_iff_mem_redP16] at h1
  exact ⟨h3, h1⟩

private theorem det_eq_one_of_isRelDegree_three (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (σ : L ≃ₐ[ℚ] L) (h : LanglandsTunnell.P5.IsRelDegree (LanglandsTunnell.sylowH e) σ 3) :
    ((e σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
  obtain ⟨h3, h1⟩ := cube_mem_redP16_and_notMem_of_isRelDegree_three e σ h
  exact det_eq_one_of_cube_mem_redP16 _ h3 h1

private theorem liftOf_det_eq_one_and_trace_mul_self (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (σ : L ≃ₐ[ℚ] L) (h : LanglandsTunnell.P5.IsRelDegree (LanglandsTunnell.sylowH e) σ 3) :
    (LanglandsTunnell.P2.liftOf (e σ)).det = 1 ∧
      (LanglandsTunnell.P2.liftOf (e σ)).trace * (LanglandsTunnell.P2.liftOf (e σ)).trace = 1 := by
  obtain ⟨h3, h1⟩ := cube_mem_redP16_and_notMem_of_isRelDegree_three e σ h
  have hred : (LanglandsTunnell.P2.liftOf (e σ)).map LanglandsTunnell.P0.redc =
      ((e σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    rw [← LanglandsTunnell.P0.map_red_eq_map_redc]
    exact LanglandsTunnell.P2.liftOf_red _
  have hK : LanglandsTunnell.P2.liftOf (e σ) ∈ LanglandsTunnell.P0.K48 :=
    (LanglandsTunnell.P0.mem_closure_iff_mem_K48 _).1 (LanglandsTunnell.P2.liftOf_mem _)
  have hent := entries_of_mem_K48_of_cube_mem_redP16 _ hK (by rw [hred]; exact h3) (by rw [hred]; exact h1)
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  exact hent

private theorem conj_notMem_sylowH_of_isRelDegree_three
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (σ : L ≃ₐ[ℚ] L)
    (h : LanglandsTunnell.P5.IsRelDegree (LanglandsTunnell.sylowH e) σ 3) (τ : L ≃ₐ[ℚ] L) :
    τ * σ * τ⁻¹ ∉ LanglandsTunnell.sylowH e := by
  intro hmem
  have h8 : (τ * σ * τ⁻¹) ^ 8 = 1 := by
    rw [LanglandsTunnell.P4.mem_sylowH_iff_mem_redP16] at hmem
    have hB := pow_eight_eq_one_of_mem_redP16 _ hmem
    apply e.injective
    rw [map_pow, map_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    simpa only [pow_succ, pow_zero, one_mul] using hB
  have hσ8 : σ ^ 8 = 1 := by
    rwa [conj_pow, conj_eq_one_iff] at h8
  have hσ : σ = (σ ^ 3) ^ 3 := by
    rw [← pow_mul, show (3 * 3 : ℕ) = 8 + 1 from rfl, pow_succ, hσ8, one_mul]
  have h1 : σ ∉ LanglandsTunnell.sylowH e := by
    have := h.2.2 1 one_pos (by norm_num)
    rwa [pow_one] at this
  have h2 : (σ ^ 3) ^ 3 ∈ LanglandsTunnell.sylowH e := (LanglandsTunnell.sylowH e).pow_mem h.2.1 3
  rw [← hσ] at h2
  exact h1 h2

variable [IsGalois ℚ L]

private theorem readoff_at_degOne (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hmem : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ H) (F : HeckeEigensystem ℚ ℂ)
    (hF : (formalBaseChange ℚ ↥(fixFld H) F).a (LanglandsTunnell.P4.placeUnderH H hℓ Q) =
        ((P2.liftTraceSeed e H).map iotaZsqrtdNegTwo).a (LanglandsTunnell.P4.placeUnderH H hℓ Q) ∧
      (formalBaseChange ℚ ↥(fixFld H) F).b (LanglandsTunnell.P4.placeUnderH H hℓ Q) =
        ((P2.liftTraceSeed e H).map iotaZsqrtdNegTwo).b (LanglandsTunnell.P4.placeUnderH H hℓ Q)) :
    F.a (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) =
        iotaZsqrtdNegTwo (P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace ∧
      F.b (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) =
        iotaZsqrtdNegTwo (P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).det := by

  have hrel : LanglandsTunnell.P2.relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) = 1 :=
    (LanglandsTunnell.P2.IsRelDegree.unique _ _ ((LanglandsTunnell.P5.isRelDegree_one_iff _ _).2 hmem)
      (LanglandsTunnell.P2.isRelDegree_relDeg _ _)).symm
  have hf : ((LanglandsTunnell.P4.placeUnderH H hℓ Q).under (𝓞 ℚ)).asIdeal.inertiaDeg'
      (LanglandsTunnell.P4.placeUnderH H hℓ Q).asIdeal = 1 := by
    rw [LanglandsTunnell.P4.inertiaDeg_eq_relDeg H hℓ Q hI _ (LanglandsTunnell.P4.placeUnderH_asIdeal H hℓ Q),
      hrel]
  have hu : (LanglandsTunnell.P4.placeUnderH H hℓ Q).under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ :=
    LanglandsTunnell.P4.placeUnderH_under H hℓ Q

  have hMred : (P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).map FLT.ExplicitLift.red =
      ((e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ 1) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    rw [pow_one]
    exact LanglandsTunnell.P2.liftOf_red _
  have ha := LanglandsTunnell.P4.isAttachedOverFixedField_liftTraceSeed' e H ∅ ℓ (Finset.notMem_empty ℓ) hℓ Q
    inferInstance inferInstance inferInstance hI 1 ((LanglandsTunnell.P5.isRelDegree_one_iff _ _).2 hmem) _
    (LanglandsTunnell.P2.liftOf_mem _) hMred _ (LanglandsTunnell.P4.placeUnderH_asIdeal H hℓ Q)
  have hb := LanglandsTunnell.P4.seed_b_eq_det' e H hℓ Q hI 1 ((LanglandsTunnell.P5.isRelDegree_one_iff _ _).2 hmem)
    _ (LanglandsTunnell.P2.liftOf_mem _) hMred _ (LanglandsTunnell.P4.placeUnderH_asIdeal H hℓ Q)
  obtain ⟨hFa, hFb⟩ := hF
  rw [formalBaseChange_a, hf, satakePow_one, hu, HeckeEigensystem.map_a] at hFa
  rw [formalBaseChange_b, hf, pow_one, hu, HeckeEigensystem.map_b] at hFb
  exact ⟨hFa.trans (congrArg iotaZsqrtdNegTwo ha), hFb.trans (congrArg iotaZsqrtdNegTwo hb)⟩

private theorem readoff_b_at_degOne (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hmem : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ H) (F : HeckeEigensystem ℚ ℂ)
    (hF : (formalBaseChange ℚ ↥(fixFld H) F).b (LanglandsTunnell.P4.placeUnderH H hℓ Q) =
        ((P2.liftTraceSeed e H).map iotaZsqrtdNegTwo).b (LanglandsTunnell.P4.placeUnderH H hℓ Q)) :
    F.b (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) =
      iotaZsqrtdNegTwo (P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).det := by
  have hrel : LanglandsTunnell.P2.relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) = 1 :=
    (LanglandsTunnell.P2.IsRelDegree.unique _ _ ((LanglandsTunnell.P5.isRelDegree_one_iff _ _).2 hmem)
      (LanglandsTunnell.P2.isRelDegree_relDeg _ _)).symm
  have hf : ((LanglandsTunnell.P4.placeUnderH H hℓ Q).under (𝓞 ℚ)).asIdeal.inertiaDeg'
      (LanglandsTunnell.P4.placeUnderH H hℓ Q).asIdeal = 1 := by
    rw [LanglandsTunnell.P4.inertiaDeg_eq_relDeg H hℓ Q hI _ (LanglandsTunnell.P4.placeUnderH_asIdeal H hℓ Q),
      hrel]
  have hu : (LanglandsTunnell.P4.placeUnderH H hℓ Q).under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ :=
    LanglandsTunnell.P4.placeUnderH_under H hℓ Q
  have hMred : (P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).map FLT.ExplicitLift.red =
      ((e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ 1) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    rw [pow_one]
    exact LanglandsTunnell.P2.liftOf_red _
  have hb := LanglandsTunnell.P4.seed_b_eq_det' e H hℓ Q hI 1 ((LanglandsTunnell.P5.isRelDegree_one_iff _ _).2 hmem)
    _ (LanglandsTunnell.P2.liftOf_mem _) hMred _ (LanglandsTunnell.P4.placeUnderH_asIdeal H hℓ Q)
  rw [formalBaseChange_b, hf, pow_one, hu, HeckeEigensystem.map_b] at hF
  exact hF.trans (congrArg iotaZsqrtdNegTwo hb)

private theorem readoff_a_at_degThree (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hrel : LanglandsTunnell.P5.IsRelDegree H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) 3) (F : HeckeEigensystem ℚ ℂ)
    (hF : (formalBaseChange ℚ ↥(fixFld H) F).a (LanglandsTunnell.P4.placeUnderH H hℓ Q) =
        ((P2.liftTraceSeed e H).map iotaZsqrtdNegTwo).a (LanglandsTunnell.P4.placeUnderH H hℓ Q)) :
    satakePow 3 (F.a (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩)) (F.b (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩)) =
      iotaZsqrtdNegTwo (P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) * P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) *
        P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace := by

  have hf : ((LanglandsTunnell.P4.placeUnderH H hℓ Q).under (𝓞 ℚ)).asIdeal.inertiaDeg'
      (LanglandsTunnell.P4.placeUnderH H hℓ Q).asIdeal = 3 := by
    rw [LanglandsTunnell.P4.inertiaDeg_eq_relDeg H hℓ Q hI _ (LanglandsTunnell.P4.placeUnderH_asIdeal H hℓ Q)]
    exact LanglandsTunnell.P2.IsRelDegree.unique _ _ (LanglandsTunnell.P2.isRelDegree_relDeg _ _) hrel
  have hu : (LanglandsTunnell.P4.placeUnderH H hℓ Q).under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ :=
    LanglandsTunnell.P4.placeUnderH_under H hℓ Q

  have ha := LanglandsTunnell.P4.isAttachedOverFixedField_liftTraceSeed' e H ∅ ℓ (Finset.notMem_empty ℓ) hℓ Q
    inferInstance inferInstance inferInstance hI 3 hrel _ (LanglandsTunnell.P2.liftOf_mem _)
    (LanglandsTunnell.P2.liftOf_red (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ 3))) _
    (LanglandsTunnell.P4.placeUnderH_asIdeal H hℓ Q)
  have hcube : P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ 3)) =
      P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) * P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) *
        P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) := by
    rw [map_pow, pow_succ, pow_two, LanglandsTunnell.P4.liftOf_mul, LanglandsTunnell.P4.liftOf_mul]
  rw [formalBaseChange_a, hf, hu, HeckeEigensystem.map_a, ha, hcube] at hF
  exact hF

private theorem ne_three_of_twisted_face (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : HeckeEigensystem ℚ ℂ) (i : Fin 2) (hi : ¬ i = 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hb : (formalBaseChange ℚ ↥(fixFld (sylowH e))
          (if i = 0 then Φ else Φ.twist fun v => iotaZsqrtdNegTwo (chiNegThreeWeight v))).b
            (LanglandsTunnell.P4.placeUnderH (sylowH e) hℓ Q) =
        ((P2.liftTraceSeed e (sylowH e)).map iotaZsqrtdNegTwo).b (LanglandsTunnell.P4.placeUnderH (sylowH e) hℓ Q)) :
    ℓ ≠ 3 := by
  rintro rfl
  have hu3 : (LanglandsTunnell.P4.placeUnderH (sylowH e) hℓ Q).under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨3, hℓ⟩ :=
    LanglandsTunnell.P4.placeUnderH_under (sylowH e) hℓ Q
  rw [if_neg hi, formalBaseChange_b,
    LanglandsTunnell.P4.inertiaDeg_eq_relDeg (sylowH e) hℓ Q hI _ (LanglandsTunnell.P4.placeUnderH_asIdeal (sylowH e) hℓ Q),
    hu3, HeckeEigensystem.map_b, HeckeEigensystem.twist_b, P5.TwistTransport.chiNegThreeWeight_ratPrime,
    LanglandsTunnell.P4.liftTraceSeed_b] at hb
  have h0 : ((EisensteinWeightOne.chiNegThree 3 : ℤ) : ℤ√(-2)) = 0 := by decide
  rw [h0, map_zero, zero_pow two_ne_zero, zero_mul,
    zero_pow (LanglandsTunnell.P2.isRelDegree_relDeg (sylowH e) _).1.ne'] at hb
  have h1 : (LanglandsTunnell.P2.liftOf (e (LanglandsTunnell.P2.seedFrob (sylowH e)
        (LanglandsTunnell.P4.placeUnderH (sylowH e) hℓ Q)))).det *
      (LanglandsTunnell.P2.liftOf (e (LanglandsTunnell.P2.seedFrob (sylowH e)
        (LanglandsTunnell.P4.placeUnderH (sylowH e) hℓ Q)))⁻¹).det = 1 := by
    rw [← Matrix.det_mul, LanglandsTunnell.P4.liftOf_mul_inv, Matrix.det_one]
  have hunit : IsUnit (LanglandsTunnell.P2.liftOf (e (LanglandsTunnell.P2.seedFrob (sylowH e)
      (LanglandsTunnell.P4.placeUnderH (sylowH e) hℓ Q)))).det :=
    ⟨⟨_, _, h1, by rwa [mul_comm] at h1⟩, rfl⟩
  exact (hunit.map iotaZsqrtdNegTwo).ne_zero hb.symm

private theorem inertiaDeg_ne_one_of_smul_eq (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hconj : ∀ τ : L ≃ₐ[ℚ] L, τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹ ∉ H)
    (Q' : Ideal (𝓞 L)) [Q'.IsPrime] [Q'.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q')]
    (τ : L ≃ₐ[ℚ] L) (hτ : τ • Q = Q')
    (u : HeightOneSpectrum (𝓞 (↥(LanglandsTunnell.P0.fixFld H))))
    (hu : u.asIdeal = Q'.under (𝓞 (↥(LanglandsTunnell.P0.fixFld H)))) :
    (u.under (𝓞 ℚ)).asIdeal.inertiaDeg' u.asIdeal ≠ 1 := by
  subst hτ
  have hI' : (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := LanglandsTunnell.P5.inertia_smul_eq_bot τ Q hI
  rw [LanglandsTunnell.P4.inertiaDeg_eq_relDeg H hℓ (τ • Q) hI' u hu, LanglandsTunnell.P5.arithFrobAt_smul τ Q hI]
  intro h1
  have hrel := LanglandsTunnell.P2.isRelDegree_relDeg H (τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹)
  rw [h1] at hrel
  exact hconj τ ((LanglandsTunnell.P5.isRelDegree_one_iff H _).1 hrel)

private theorem inertiaDeg_ne_one_of_forall_conj_notMem (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hconj : ∀ τ : L ≃ₐ[ℚ] L, τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹ ∉ H)
    (u : HeightOneSpectrum (𝓞 (↥(LanglandsTunnell.P0.fixFld H))))
    (hu : u.under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) :
    (u.under (𝓞 ℚ)).asIdeal.inertiaDeg' u.asIdeal ≠ 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  have hℓu : ((ℓ : ℕ) : 𝓞 (↥(LanglandsTunnell.P0.fixFld H))) ∈ u.asIdeal :=
    LanglandsTunnell.P5.natCast_mem_of_under_eq_ratPrime u hℓ hu
  have hℓQ' : ((ℓ : ℕ) : 𝓞 L) ∈ LanglandsTunnell.P2.primeOver H u := by
    rw [← LanglandsTunnell.P2.under_primeOver H u] at hℓu
    have h := Ideal.mem_comap.1 hℓu
    rwa [map_natCast] at h
  haveI hQ' : (LanglandsTunnell.P2.primeOver H u).LiesOver (ratPrimeIdeal ℓ) :=
    ⟨Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ _)) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact hℓQ')⟩

  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (ratPrimeIdeal ℓ) Q (LanglandsTunnell.P2.primeOver H u)
    (L ≃ₐ[ℚ] L)
  exact inertiaDeg_ne_one_of_smul_eq H hℓ Q hI hconj (LanglandsTunnell.P2.primeOver H u) τ hτ u
    (LanglandsTunnell.P2.under_primeOver H u).symm

end LanglandsTunnell.ReadoffSol
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell.P4"

open NumberField IsDedekindDomain AutomorphicForm FrobeniusDensity _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH.LanglandsTunnell LanglandsTunnell.ReadoffSol in
open scoped Pointwise in

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ) (i : Fin 2)
    {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] [Finite (NumberField.RingOfIntegers L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hE : ∀ w : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))),
      w.under (NumberField.RingOfIntegers ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ →
      (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) Φ).b w =
        ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.detKer e)).map
          AutomorphicForm.iotaZsqrtdNegTwo).b w)
    (hE₃ : ∀ u : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))),
      u.under (NumberField.RingOfIntegers ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ →
      (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
            (if i = 0 then Φ else
              Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v))).a u =
          ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.sylowH e)).map
            AutomorphicForm.iotaZsqrtdNegTwo).a u ∧
        (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))
            (if i = 0 then Φ else
              Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v))).b u =
          ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.sylowH e)).map
            AutomorphicForm.iotaZsqrtdNegTwo).b u) :
    ∃ M ∈ Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (Zsqrtd (-2)))),
      M.map FLT.ExplicitLift.red
          = ((e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)) ∧
        (if i = 0 then Φ else
            Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)).b
            (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) = AutomorphicForm.iotaZsqrtdNegTwo M.det ∧
        ((if i = 0 then Φ else
            Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)).a
            (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) = AutomorphicForm.iotaZsqrtdNegTwo M.trace ∨
          ((∀ u : IsDedekindDomain.HeightOneSpectrum
                (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))),
              u.under (NumberField.RingOfIntegers ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩ →
              (u.under (NumberField.RingOfIntegers ℚ)).asIdeal.inertiaDeg' u.asIdeal ≠ 1) ∧
            (if i = 0 then Φ else
            Φ.twist fun v => AutomorphicForm.iotaZsqrtdNegTwo (LanglandsTunnell.chiNegThreeWeight v)).a
              (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) = AutomorphicForm.iotaZsqrtdNegTwo (-2 * M.trace))) := by
  classical

  refine ⟨LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)), LanglandsTunnell.P2.liftOf_mem _,
    LanglandsTunnell.P2.liftOf_red _, ?_⟩

  rcases LanglandsTunnell.P4.exists_conj_mem_sylowH_or_isRelDegree_three e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) with
    ⟨τ, hτ⟩ | hrel
  ·

    haveI : Finite (𝓞 L ⧸ τ • Q) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    have hIτ : (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := LanglandsTunnell.P5.inertia_smul_eq_bot τ Q hI
    have hFrob : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q) = τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹ :=
      LanglandsTunnell.P5.arithFrobAt_smul τ Q hI
    have hmem : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q) ∈ sylowH e := by
      rw [hFrob]
      exact hτ
    have hread := readoff_at_degOne e (sylowH e) hℓ (τ • Q) hIτ hmem _
      (hE₃ _ (LanglandsTunnell.P4.placeUnderH_under (sylowH e) hℓ (τ • Q)))

    have heτ : e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)) = e τ * e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) * (e τ)⁻¹ := by
      rw [hFrob, map_mul, map_mul, map_inv]
    rw [heτ, LanglandsTunnell.P4.trace_liftOf_conj, LanglandsTunnell.P4.det_liftOf_conj] at hread
    exact ⟨hread.2, Or.inl hread.1⟩
  ·

    have hdet1 := det_eq_one_of_isRelDegree_three e _ hrel
    have hσE : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ detKer e := (mem_detKer_iff e _).2 hdet1
    have hΦb := readoff_b_at_degOne e (detKer e) hℓ Q hI hσE Φ
      (hE _ (LanglandsTunnell.P4.placeUnderH_under (detKer e) hℓ Q))

    have hFb : (if i = 0 then Φ else Φ.twist fun v => iotaZsqrtdNegTwo (chiNegThreeWeight v)).b
        (AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) =
          iotaZsqrtdNegTwo (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).det := by
      by_cases hi : i = 0
      · rw [if_pos hi]
        exact hΦb
      · have hℓ3 : ℓ ≠ 3 := ne_three_of_twisted_face e Φ i hi hℓ Q hI
          (hE₃ _ (LanglandsTunnell.P4.placeUnderH_under (sylowH e) hℓ Q)).2
        rw [if_neg hi, HeckeEigensystem.twist_b, ← map_pow, chiNegThreeWeight_sq_eq_one hℓ hℓ3, map_one, one_mul]
        exact hΦb
    refine ⟨hFb, ?_⟩

    obtain ⟨hd, ht⟩ := liftOf_det_eq_one_and_trace_mul_self e _ hrel
    have ha := readoff_a_at_degThree e (sylowH e) hℓ Q hI hrel _
      (hE₃ _ (LanglandsTunnell.P4.placeUnderH_under (sylowH e) hℓ Q)).1
    rw [hFb, hd, map_one, trace_cube_fin_two, hd] at ha
    have hpartner : (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace ^ 3 -
        3 * 1 * (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace =
          -2 * (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace := by
      linear_combination (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace * ht
    have hι : iotaZsqrtdNegTwo (-2 * (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace) =
        -2 * iotaZsqrtdNegTwo (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace := by
      rw [map_mul, map_neg, map_ofNat]
    rw [hpartner, hι] at ha
    have hs : iotaZsqrtdNegTwo (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace *
        iotaZsqrtdNegTwo (LanglandsTunnell.P2.liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))).trace = 1 := by
      rw [← map_mul, ht, map_one]
    rcases eq_or_eq_of_satakePow_three _ _ hs ha with h | h
    · exact Or.inl h
    ·
      refine Or.inr ⟨fun u hu => inertiaDeg_ne_one_of_forall_conj_notMem (sylowH e) hℓ Q hI
        (conj_notMem_sylowH_of_isRelDegree_three e _ hrel) u hu, ?_⟩
      rw [h, hι]

end S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH
end P2MW
export P2MW.S_LanglandsTunnell_face_liftValuedUpToPartner_of_b_agreesAt_liftTraceSeed_detKer_sylowH (solution)
