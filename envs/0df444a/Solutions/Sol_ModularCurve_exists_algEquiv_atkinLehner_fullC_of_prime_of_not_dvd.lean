-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d8336b83-4706-524c-b9c8-fd18d376194e

import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.CharP.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve Polynomial TensorProduct

namespace AtkinLehnerC

section O1

variable (N p : ℕ) [NeZero p]

private def gen (e : ℕ) [NeZero e] (he : e ∣ N * p) : modularFunctionFieldFull (N * p) :=
  ⟨qExpand ℚ e jq, jqd_mem_full (N * p) he⟩

omit [NeZero p] in
private theorem neZero_of_dvd [NeZero (N * p)] {e : ℕ} (he : e ∣ N * p) : NeZero e :=
  ⟨fun h => by subst h; exact NeZero.ne (N * p) (Nat.eq_zero_of_zero_dvd he)⟩

omit [NeZero p] in

private theorem dvd_or_eq_mul_of_dvd_mul (hp : p.Prime) {e : ℕ} (he : e ∣ N * p) :
    e ∣ N ∨ ∃ d, d ∣ N ∧ e = d * p := by
  by_cases hpe : p ∣ e
  · obtain ⟨d, rfl⟩ := hpe
    refine Or.inr ⟨d, ?_, mul_comm _ _⟩
    rw [mul_comm N p] at he
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos he
  · exact Or.inl (Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpe).symm he)

variable (σ : modularFunctionFieldFull (N * p) ≃ₐ[ℚ] modularFunctionFieldFull (N * p))
  (hσ : IsAtkinLehnerAutFull N p σ) (hp : p.Prime)
include hσ hp

private theorem exists_apply_gen (e : ℕ) [NeZero e] (he : e ∣ N * p) :
    ∃ (e' : ℕ) (_ : NeZero e') (he' : e' ∣ N * p),
      σ (gen N p e he) = gen N p e' he' ∧ σ (gen N p e' he') = gen N p e he := by
  rcases dvd_or_eq_mul_of_dvd_mul N p hp he with hd | ⟨d, hd, rfl⟩
  · exact ⟨e * p, inferInstance, Nat.mul_dvd_mul_right hd p, (hσ e ‹_› hd).1, (hσ e ‹_› hd).2⟩
  · haveI : NeZero d := ⟨fun h => by subst h; exact NeZero.ne (0 * p) (by simp)⟩
    exact ⟨d, inferInstance, Dvd.dvd.mul_right hd p, (hσ d ‹_› hd).2, (hσ d ‹_› hd).1⟩

private theorem apply_apply (x : modularFunctionFieldFull (N * p)) : σ (σ x) = x := by
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨e, he0, he, rfl⟩ := hy
    obtain ⟨e', _, he', h1, h2⟩ := exists_apply_gen N p σ hσ hp e he
    show σ (σ (gen N p e he)) = gen N p e he
    rw [h1, h2]
  | algebraMap c =>
    have hc : (⟨algebraMap ℚ (LaurentSeries ℚ) c, IntermediateField.algebraMap_mem _ c⟩ :
        modularFunctionFieldFull (N * p)) = (c : modularFunctionFieldFull (N * p)) :=
      Subtype.ext (by
        show algebraMap ℚ (LaurentSeries ℚ) c = ((c : modularFunctionFieldFull (N * p)) : LaurentSeries ℚ)
        rw [SubfieldClass.coe_ratCast, eq_ratCast])
    rw [hc, map_ratCast, map_ratCast]
  | add y z _ _ hy hz =>
    have := congrArg₂ (· + ·) hy hz
    simp only [← map_add] at this
    exact this
  | inv y _ hy =>
    have := congrArg (·⁻¹) hy
    simp only [← map_inv₀] at this
    exact this
  | mul y z _ _ hy hz =>
    have := congrArg₂ (· * ·) hy hz
    simp only [← map_mul] at this
    exact this

private def genRing : Subring (modularFunctionFieldFull (N * p)) :=
  Subring.closure {x | ∃ (e : ℕ) (_ : NeZero e) (he : e ∣ N * p), x = gen N p e he}

omit [NeZero p] hσ hp in
private theorem gen_mem_genRing (e : ℕ) [NeZero e] (he : e ∣ N * p) : gen N p e he ∈ genRing N p :=
  Subring.subset_closure ⟨e, ‹_›, he, rfl⟩

private theorem apply_mem_genRing {x : modularFunctionFieldFull (N * p)} (hx : x ∈ genRing N p) : σ x ∈ genRing N p := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨e, _, he, rfl⟩ := hy
    obtain ⟨e', _, he', h1, -⟩ := exists_apply_gen N p σ hσ hp e he
    rw [h1]
    exact gen_mem_genRing N p e' he'
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

private def genRingAut : genRing N p ≃+* genRing N p where
  toFun x := ⟨σ (x : modularFunctionFieldFull (N * p)), apply_mem_genRing N p σ hσ hp x.2⟩
  invFun x := ⟨σ (x : modularFunctionFieldFull (N * p)), apply_mem_genRing N p σ hσ hp x.2⟩
  left_inv x := Subtype.ext (apply_apply N p σ hσ hp x)
  right_inv x := Subtype.ext (apply_apply N p σ hσ hp x)
  map_mul' x y := Subtype.ext (map_mul σ (x : modularFunctionFieldFull (N * p)) y)
  map_add' x y := Subtype.ext (map_add σ (x : modularFunctionFieldFull (N * p)) y)

private theorem genRingAut_gen (e : ℕ) [NeZero e] (he : e ∣ N * p) :
    ∃ (e' : ℕ) (_ : NeZero e') (he' : e' ∣ N * p),
      genRingAut N p σ hσ hp ⟨gen N p e he, gen_mem_genRing N p e he⟩ = ⟨gen N p e' he', gen_mem_genRing N p e' he'⟩
        ∧ genRingAut N p σ hσ hp ⟨gen N p e' he', gen_mem_genRing N p e' he'⟩
          = ⟨gen N p e he, gen_mem_genRing N p e he⟩ := by
  obtain ⟨e', _, he', h1, h2⟩ := exists_apply_gen N p σ hσ hp e he
  exact ⟨e', ‹_›, he', Subtype.ext h1, Subtype.ext h2⟩

private theorem genRingAut_gen_of_dvd (d : ℕ) [NeZero d] (hd : d ∣ N) :
    genRingAut N p σ hσ hp ⟨gen N p d (Dvd.dvd.mul_right hd p), gen_mem_genRing N p _ _⟩
        = ⟨gen N p (d * p) (Nat.mul_dvd_mul_right hd p), gen_mem_genRing N p _ _⟩
      ∧ genRingAut N p σ hσ hp ⟨gen N p (d * p) (Nat.mul_dvd_mul_right hd p), gen_mem_genRing N p _ _⟩
        = ⟨gen N p d (Dvd.dvd.mul_right hd p), gen_mem_genRing N p _ _⟩ :=
  ⟨Subtype.ext (hσ d ‹_› hd).1, Subtype.ext (hσ d ‹_› hd).2⟩

private theorem genRingAut_apply_apply (x : genRing N p) : genRingAut N p σ hσ hp (genRingAut N p σ hσ hp x) = x :=
  Subtype.ext (apply_apply N p σ hσ hp (x : modularFunctionFieldFull (N * p)))

end O1

section RedMap

universe u v

variable {k : Type u} [Field k]
variable {R : Type v} [CommRing R]
variable {L : Type u} [CommRing L] [Algebra k L]

private noncomputable def redMap (ρ : R →ₐ[ℤ] L) : k ⊗[ℤ] R →ₐ[k] L :=
  Algebra.TensorProduct.lift (Algebra.ofId k L) ρ fun _ _ => Commute.all _ _

private theorem redMap_tmul (ρ : R →ₐ[ℤ] L) (c : k) (r : R) : redMap ρ (c ⊗ₜ r) = algebraMap k L c * ρ r :=
  Algebra.TensorProduct.lift_tmul _ _ _ c r

private theorem redMap_one_tmul (ρ : R →ₐ[ℤ] L) (r : R) : redMap ρ ((1 : k) ⊗ₜ[ℤ] r) = ρ r := by
  rw [redMap_tmul, map_one, one_mul]

end RedMap

section IntLift

variable (N p : ℕ)
variable (K : Type*) [Field K]

private abbrev ιK : LaurentSeries ℤ →+* LaurentSeries K := coeffMap (Int.castRingHom K)

private theorem ιK_injective [CharZero K] : Function.Injective (ιK K) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries K => z.coeff n) h
  simp only [coeffMap_coeff, eq_intCast] at this
  exact Int.cast_injective this

private theorem ιK_qExpand_jq (e : ℕ) [NeZero e] : ιK K (qExpand ℤ e (jqModC ℤ)) = qExpand K e (jqModC K) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

private def θ : genRing N p →+* LaurentSeries ℚ :=
  (SubringClass.subtype (modularFunctionFieldFull (N * p))).comp (genRing N p).subtype

private theorem θ_apply (x : genRing N p) :
    θ N p x = ((x : modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) := rfl

private theorem θ_injective : Function.Injective (θ N p) := fun x y h =>
  Subtype.ext (Subtype.ext (by rwa [θ_apply, θ_apply] at h))

private theorem θ_gen (e : ℕ) [NeZero e] (he : e ∣ N * p) :
    θ N p ⟨gen N p e he, gen_mem_genRing N p e he⟩ = qExpand ℚ e (jqModC ℚ) := by
  rw [θ_apply, jqModC_rat]
  rfl

private theorem θ_mem_range (x : genRing N p) : ∃ z : LaurentSeries ℤ, ιK ℚ z = θ N p x := by
  obtain ⟨x, hx⟩ := x
  rw [θ_apply]
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨e, _, he, rfl⟩ := hy
    exact ⟨qExpand ℤ e (jqModC ℤ), by rw [ιK_qExpand_jq, ← θ_gen N p e he, θ_apply]⟩
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | one => exact ⟨1, by rw [map_one]; rfl⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  | neg y _ hy =>
    obtain ⟨a, ha⟩ := hy
    exact ⟨-a, by rw [map_neg, ha]; rfl⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩

private def pre (x : genRing N p) : LaurentSeries ℤ := (θ_mem_range N p x).choose

private theorem ιK_pre (x : genRing N p) : ιK ℚ (pre N p x) = θ N p x := (θ_mem_range N p x).choose_spec

private theorem pre_eq_of_eq (x : genRing N p) (z : LaurentSeries ℤ) (hz : ιK ℚ z = θ N p x) : pre N p x = z :=
  ιK_injective ℚ (by rw [ιK_pre, hz])

private def ρ : genRing N p →+* LaurentSeries K where
  toFun x := ιK K (pre N p x)
  map_one' := by rw [pre_eq_of_eq N p 1 1 (by rw [map_one, map_one]), map_one]
  map_mul' x y := by
    have h : ιK ℚ (pre N p x * pre N p y) = θ N p (x * y) := by
      rw [RingHom.map_mul, ιK_pre, ιK_pre, RingHom.map_mul]
    rw [← RingHom.map_mul, pre_eq_of_eq N p (x * y) (pre N p x * pre N p y) h]
  map_zero' := by rw [pre_eq_of_eq N p 0 0 (by rw [map_zero, map_zero]), map_zero]
  map_add' x y := by
    have h : ιK ℚ (pre N p x + pre N p y) = θ N p (x + y) := by
      rw [RingHom.map_add, ιK_pre, ιK_pre, RingHom.map_add]
    rw [← RingHom.map_add, pre_eq_of_eq N p (x + y) (pre N p x + pre N p y) h]

private theorem ρ_apply (x : genRing N p) : ρ N p K x = ιK K (pre N p x) := rfl

private theorem ρ_eq_of_eq (x : genRing N p) (z : LaurentSeries ℤ) (hz : ιK ℚ z = θ N p x) : ρ N p K x = ιK K z := by
  rw [ρ_apply, pre_eq_of_eq N p x z hz]

private theorem ρ_gen (e : ℕ) [NeZero e] (he : e ∣ N * p) :
    ρ N p K ⟨gen N p e he, gen_mem_genRing N p e he⟩ = qExpand K e (jqModC K) := by
  rw [ρ_eq_of_eq N p K _ (qExpand ℤ e (jqModC ℤ)) (by rw [ιK_qExpand_jq, θ_gen]), ιK_qExpand_jq]

private def ρₐ := (ρ N p K).toIntAlgHom

private theorem ρₐ_apply (x : genRing N p) : ρₐ N p K x = ρ N p K x := rfl

end IntLift

section Descent

variable (N p : ℕ) [NeZero p]
variable (σ : modularFunctionFieldFull (N * p) ≃ₐ[ℚ] modularFunctionFieldFull (N * p))
  (hσ : IsAtkinLehnerAutFull N p σ) (hp : p.Prime)
variable (K : Type*) [Field K]

private def σR := (genRingAut N p σ hσ hp).toRingHom.toIntAlgHom

private theorem σR_apply (x : genRing N p) : σR N p σ hσ hp x = genRingAut N p σ hσ hp x := rfl

private theorem σR_σR (x : genRing N p) : σR N p σ hσ hp (σR N p σ hσ hp x) = x :=
  genRingAut_apply_apply N p σ hσ hp x

private def τ := Algebra.TensorProduct.map (AlgHom.id K K) (σR N p σ hσ hp)

private theorem τ_tmul (c : K) (r : genRing N p) : τ N p σ hσ hp K (c ⊗ₜ r) = c ⊗ₜ σR N p σ hσ hp r := by
  simp [τ]

private theorem τ_τ (x : K ⊗[ℤ] genRing N p) : τ N p σ hσ hp K (τ N p σ hσ hp K x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c r => rw [τ_tmul, τ_tmul, σR_σR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private def jR : genRing N p := ⟨gen N p 1 (one_dvd _), gen_mem_genRing N p 1 (one_dvd _)⟩

omit [NeZero p] in
private theorem ρ_jR : ρ N p K (jR N p) = jqModC K := by
  rw [jR, ρ_gen, qExpand_one_apply]

private theorem ρ_σR_jR : ρ N p K (σR N p σ hσ hp (jR N p)) = qExpand K (1 * p) (jqModC K) := by
  rw [jR, σR_apply, (genRingAut_gen_of_dvd N p σ hσ hp 1 (one_dvd N)).1, ρ_gen]

private theorem redMap_τ_eq_zero
    (htors : ∀ x : K ⊗[ℤ] genRing N p, redMap (ρₐ N p K) x = 0 →
      ∃ f : K[X], f ≠ 0 ∧ aeval ((1 : K) ⊗ₜ[ℤ] jR N p) f * x = 0)
    (x : K ⊗[ℤ] genRing N p) (hx : redMap (ρₐ N p K) x = 0) :
    redMap (ρₐ N p K) (τ N p σ hσ hp K x) = 0 := by
  obtain ⟨f, hf0, hfx⟩ := htors x hx
  have h1 := congrArg (fun y => redMap (ρₐ N p K) (τ N p σ hσ hp K y)) hfx
  simp only [map_mul, map_zero] at h1
  have h2 : redMap (ρₐ N p K) (τ N p σ hσ hp K (aeval ((1 : K) ⊗ₜ[ℤ] jR N p) f))
      = aeval (qExpand K (1 * p) (jqModC K)) f := by
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, τ_tmul, redMap_one_tmul, ρₐ_apply, ρ_σR_jR]
  rw [h2] at h1
  have h3 : aeval (qExpand K (1 * p) (jqModC K)) f ≠ 0 := by
    rw [← qExpandAlgHomC_apply, aeval_algHom_apply, qExpandAlgHomC_apply]
    intro h0
    exact hf0 (transcendental_iff.mp (transcendental_jqModC K) f ((qExpand_injective (1 * p)) (by
      rw [h0, map_zero])))
  exact (mul_eq_zero.mp h1).resolve_left h3

private def B : Subalgebra K (LaurentSeries K) := (redMap (ρₐ N p K)).range

private def πB : K ⊗[ℤ] genRing N p →ₐ[K] B N p K := (redMap (ρₐ N p K)).rangeRestrict

omit [NeZero p] in
private theorem πB_surjective : Function.Surjective (πB N p K) := AlgHom.rangeRestrict_surjective _

omit [NeZero p] in
private theorem coe_πB (x : K ⊗[ℤ] genRing N p) : (πB N p K x : LaurentSeries K) = redMap (ρₐ N p K) x := rfl

private def σB (htors : ∀ x : K ⊗[ℤ] genRing N p, redMap (ρₐ N p K) x = 0 →
      ∃ f : K[X], f ≠ 0 ∧ aeval ((1 : K) ⊗ₜ[ℤ] jR N p) f * x = 0) : B N p K →ₐ[K] B N p K :=
  AlgHom.liftOfSurjective (πB N p K) (πB_surjective N p K) ((πB N p K).comp (τ N p σ hσ hp K)) fun x hx => by
    rw [RingHom.mem_ker] at hx ⊢
    have hx' : redMap (ρₐ N p K) x = 0 := by rw [← coe_πB]; exact congrArg Subtype.val hx
    exact Subtype.ext (redMap_τ_eq_zero N p σ hσ hp K htors x hx')

variable (htors : ∀ x : K ⊗[ℤ] genRing N p, redMap (ρₐ N p K) x = 0 →
      ∃ f : K[X], f ≠ 0 ∧ aeval ((1 : K) ⊗ₜ[ℤ] jR N p) f * x = 0)

private theorem σB_πB (x : K ⊗[ℤ] genRing N p) :
    σB N p σ hσ hp K htors (πB N p K x) = πB N p K (τ N p σ hσ hp K x) :=
  AlgHom.liftOfSurjective_apply _ _ _ _ x

private theorem σB_σB (b : B N p K) : σB N p σ hσ hp K htors (σB N p σ hσ hp K htors b) = b := by
  obtain ⟨x, rfl⟩ := πB_surjective N p K b
  rw [σB_πB, σB_πB, τ_τ]

private def σBE : B N p K ≃ₐ[K] B N p K :=
  AlgEquiv.ofAlgHom (σB N p σ hσ hp K htors) (σB N p σ hσ hp K htors)
    (AlgHom.ext (σB_σB N p σ hσ hp K htors)) (AlgHom.ext (σB_σB N p σ hσ hp K htors))

private theorem σBE_apply (b : B N p K) : σBE N p σ hσ hp K htors b = σB N p σ hσ hp K htors b := rfl

omit [NeZero p] in
private theorem ρ_mem_adjoin (x : genRing N p) : ρ N p K x ∈ Algebra.adjoin K (divisorExpansionsC K (N * p)) := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨e, _, he, rfl⟩ := hy
    rw [ρ_gen]
    exact Algebra.subset_adjoin ⟨e, inferInstance, he, rfl⟩
  | zero => rw [show (⟨0, zero_mem _⟩ : genRing N p) = 0 from rfl, RingHom.map_zero]; exact zero_mem _
  | one => rw [show (⟨1, one_mem _⟩ : genRing N p) = 1 from rfl, RingHom.map_one]; exact one_mem _
  | add y z hy' hz' hy hz =>
    have : (⟨y + z, add_mem hy' hz'⟩ : genRing N p) = ⟨y, hy'⟩ + ⟨z, hz'⟩ := rfl
    rw [this, RingHom.map_add]
    exact add_mem hy hz
  | neg y hy' hy =>
    have : (⟨-y, neg_mem hy'⟩ : genRing N p) = -⟨y, hy'⟩ := rfl
    rw [this, RingHom.map_neg]
    exact neg_mem hy
  | mul y z hy' hz' hy hz =>
    have : (⟨y * z, mul_mem hy' hz'⟩ : genRing N p) = ⟨y, hy'⟩ * ⟨z, hz'⟩ := rfl
    rw [this, RingHom.map_mul]
    exact mul_mem hy hz

omit [NeZero p] in
private theorem B_eq_adjoin : B N p K = Algebra.adjoin K (divisorExpansionsC K (N * p)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul c r =>
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, redMap_tmul, ρₐ_apply]
      exact Subalgebra.smul_mem _ (ρ_mem_adjoin N p K r) c
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨e, _, he, rfl⟩
    exact ⟨(1 : K) ⊗ₜ ⟨gen N p e (he), gen_mem_genRing N p e he⟩, by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, redMap_one_tmul, ρₐ_apply, ρ_gen]⟩

private def σC : Algebra.adjoin K (divisorExpansionsC K (N * p)) ≃ₐ[K] Algebra.adjoin K (divisorExpansionsC K (N * p)) :=
  ((Subalgebra.equivOfEq _ _ (B_eq_adjoin N p K)).symm.trans (σBE N p σ hσ hp K htors)).trans
    (Subalgebra.equivOfEq _ _ (B_eq_adjoin N p K))

private theorem coe_σC_gen (e : ℕ) [NeZero e] (he : e ∣ N * p)
    (hmem : qExpand K e (jqModC K) ∈ Algebra.adjoin K (divisorExpansionsC K (N * p))) :
    ((σC N p σ hσ hp K htors ⟨qExpand K e (jqModC K), hmem⟩ : Algebra.adjoin K (divisorExpansionsC K (N * p)))
        : LaurentSeries K)
      = ρ N p K (σR N p σ hσ hp ⟨gen N p e he, gen_mem_genRing N p e he⟩) := by
  have hπ : πB N p K ((1 : K) ⊗ₜ ⟨gen N p e he, gen_mem_genRing N p e he⟩)
      = ⟨qExpand K e (jqModC K), by rw [B_eq_adjoin]; exact hmem⟩ :=
    Subtype.ext (by rw [coe_πB, redMap_one_tmul, ρₐ_apply, ρ_gen])
  have h1 : (Subalgebra.equivOfEq _ _ (B_eq_adjoin N p K)).symm ⟨qExpand K e (jqModC K), hmem⟩
      = πB N p K ((1 : K) ⊗ₜ ⟨gen N p e he, gen_mem_genRing N p e he⟩) := by
    rw [hπ]; rfl
  simp only [σC, AlgEquiv.trans_apply]
  rw [h1, σBE_apply, σB_πB, τ_tmul]
  show ((πB N p K _ : B N p K) : LaurentSeries K) = _
  rw [coe_πB, redMap_one_tmul, ρₐ_apply]

end Descent

section Relations

variable (M : ℕ)

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra"

private abbrev jF : modularFunctionFieldFullC ℚ M := ⟨jqModC ℚ, jqModC_mem_full ℚ M⟩

private abbrev KJ : IntermediateField ℚ (modularFunctionFieldFullC ℚ M) :=
  IntermediateField.adjoin ℚ ({jF M} : Set (modularFunctionFieldFullC ℚ M))

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance algKJ : Algebra (KJ M) (modularFunctionFieldFullC ℚ M) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance modKJ : Module (KJ M) (modularFunctionFieldFullC ℚ M) := inferInstance

private scoped instance freeKJ : Module.Free (KJ M) (modularFunctionFieldFullC ℚ M) := Module.Free.of_divisionRing _ _

private theorem finrank_full [NeZero M] :
    Module.finrank (KJ M) (modularFunctionFieldFullC ℚ M) = dedekindPsi M :=
  finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi ℚ M (by exact_mod_cast NeZero.ne M)

private theorem dedekindPsi_pos [NeZero M] : 0 < dedekindPsi M := by
  unfold dedekindPsi
  have h1 : 1 ∈ M.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne M]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1)
  simpa using Nat.pos_of_ne_zero (NeZero.ne M)

section Steps

variable {M}
variable {n : ℕ} (m : Fin (n + 1) → modularFunctionFieldFullC ℚ M)

private theorem exists_rat_poly_relation
    (g : Fin (n + 1) → KJ M)
    (hg : ∑ i, g i • m i = 0) (i₀ : Fin (n + 1)) (hi₀ : g i₀ ≠ 0) :
    ∃ P : Fin (n + 1) → ℚ[X], P i₀ ≠ 0 ∧ ∑ i, aeval (jF M) (P i) * m i = 0 := by
  classical

  obtain ⟨r, s, hs, hrs⟩ : ∃ r s : Fin (n + 1) → ℚ[X], (∀ i, aeval (jF M) (s i) ≠ 0) ∧
      ∀ i, ((g i : modularFunctionFieldFullC ℚ M)) * aeval (jF M) (s i) = aeval (jF M) (r i) := by
    have hK : ∀ i, ∃ r s : ℚ[X], ((g i : modularFunctionFieldFullC ℚ M)) = aeval (jF M) r / aeval (jF M) s :=
      fun i => (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (α := jF M) _).mp (g i).2
    choose r s hrs using hK
    refine ⟨fun i => if g i = 0 then 0 else r i, fun i => if g i = 0 then 1 else s i, fun i => ?_, fun i => ?_⟩
    · by_cases h : g i = 0
      · simp [h]
      · simp only [h, if_false]
        intro h0
        apply h
        have : ((g i : modularFunctionFieldFullC ℚ M)) = 0 := by rw [hrs i, h0, div_zero]
        exact_mod_cast this
    · by_cases h : g i = 0
      · simp [h]
      · have hsi : aeval (jF M) (s i) ≠ 0 := by
          intro h0
          apply h
          have : ((g i : modularFunctionFieldFullC ℚ M)) = 0 := by rw [hrs i, h0, div_zero]
          exact_mod_cast this
        simp only [h, if_false]
        rw [hrs i, div_mul_cancel₀ _ hsi]

  obtain ⟨T, hT0, hT⟩ : ∃ T : modularFunctionFieldFullC ℚ M, T ≠ 0 ∧
      ∀ i, aeval (jF M) (r i * ∏ i' ∈ Finset.univ.erase i, s i') = (g i : modularFunctionFieldFullC ℚ M) * T := by
    refine ⟨∏ i', aeval (jF M) (s i'), Finset.prod_ne_zero_iff.mpr fun i' _ => hs i', fun i => ?_⟩
    rw [map_mul, map_prod, ← hrs i, mul_assoc,
      Finset.mul_prod_erase Finset.univ (fun i' => aeval (jF M) (s i')) (Finset.mem_univ i)]
  refine ⟨fun i => r i * ∏ i' ∈ Finset.univ.erase i, s i', fun h => ?_, ?_⟩
  · have := hT i₀
    beta_reduce at h
    rw [h, map_zero] at this
    exact mul_ne_zero (by exact_mod_cast hi₀) hT0 this.symm
  · have h1 : ∑ i, aeval (jF M) (r i * ∏ i' ∈ Finset.univ.erase i, s i') * m i
        = T * ∑ i, (g i : modularFunctionFieldFullC ℚ M) * m i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hT i]; ring
    rw [h1]
    have h2 : ∑ i, (g i : modularFunctionFieldFullC ℚ M) * m i = ∑ i, g i • m i := rfl
    rw [h2, hg, mul_zero]

private theorem exists_int_poly_relation (P : Fin (n + 1) → ℚ[X]) (i₀ : Fin (n + 1)) (hP0 : P i₀ ≠ 0)
    (hrel : ∑ i, aeval (jF M) (P i) * m i = 0) :
    ∃ a : Fin (n + 1) → ℤ[X], a i₀ ≠ 0 ∧ ∑ i, aeval (jF M) (a i) * m i = 0 := by
  classical
  have hnorm : ∀ i, ∃ (b : ℤ) (q : ℤ[X]), b ≠ 0 ∧ q.map (Int.castRingHom ℚ) = C (b : ℚ) * P i := by
    intro i
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (P i)
    refine ⟨b, IsLocalization.integerNormalization (nonZeroDivisors ℤ) (P i), nonZeroDivisors.ne_zero hbM, ?_⟩
    rw [algebraMap_int_eq] at hb
    rw [hb]
    ext k
    simp [Algebra.smul_def]
  choose b q hb hq using hnorm
  obtain ⟨B, hB0, a, ha⟩ : ∃ B : ℤ, B ≠ 0 ∧ ∃ a : Fin (n + 1) → ℤ[X],
      ∀ i, (a i).map (Int.castRingHom ℚ) = C (B : ℚ) * P i := by
    refine ⟨∏ i', b i', Finset.prod_ne_zero_iff.mpr fun i' _ => hb i',
      fun i => C (∏ i' ∈ Finset.univ.erase i, b i') * q i, fun i => ?_⟩
    rw [Polynomial.map_mul, map_C, hq, ← mul_assoc, ← map_mul C,
      ← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)]
    congr 2
    simp only [eq_intCast, Int.cast_mul, Int.cast_prod]
    ring
  refine ⟨a, fun h => ?_, ?_⟩
  · have := ha i₀
    rw [h, Polynomial.map_zero] at this
    exact mul_ne_zero (C_ne_zero.mpr (Int.cast_ne_zero.mpr hB0)) hP0 this.symm
  · have h1 : ∀ i, aeval (jF M) (a i) = algebraMap ℚ _ (B : ℚ) * aeval (jF M) (P i) := by
      intro i
      rw [← aeval_map_algebraMap ℚ (jF M) (a i), algebraMap_int_eq, ha, map_mul, aeval_C]
    simp_rw [h1, mul_assoc, ← Finset.mul_sum, hrel, mul_zero]

private theorem exists_coprime_int_poly_relation (ℓ : ℕ) (hℓ : ℓ ≠ 1) (a₁ : Fin (n + 1) → ℤ[X]) (i₀ : Fin (n + 1))
    (ha₁0 : a₁ i₀ ≠ 0) (hrel₁ : ∑ i, aeval (jF M) (a₁ i) * m i = 0) :
    ∃ a : Fin (n + 1) → ℤ[X], (∃ i k, ¬ (ℓ : ℤ) ∣ (a i).coeff k) ∧ ∑ i, aeval (jF M) (a i) * m i = 0 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ i, (a₁ i).natDegree ≤ D :=
    ⟨Finset.univ.sup fun i => (a₁ i).natDegree, fun i => Finset.le_sup (f := fun i => (a₁ i).natDegree)
      (Finset.mem_univ i)⟩
  obtain ⟨G, hG0, hGdvd, hGmax⟩ : ∃ G : ℤ, G ≠ 0 ∧ (∀ i k, G ∣ (a₁ i).coeff k) ∧
      ∀ G' : ℤ, (∀ i k, G' ∣ (a₁ i).coeff k) → G' ∣ G := by
    refine ⟨(Finset.univ ×ˢ Finset.range (D + 1)).gcd fun t => (a₁ t.1).coeff t.2, fun hG => ?_, fun i k => ?_,
      fun G' hG' => Finset.dvd_gcd fun t _ => hG' t.1 t.2⟩
    · apply ha₁0
      ext k
      rw [coeff_zero]
      by_cases hk : k ≤ D
      · exact Finset.gcd_eq_zero_iff.mp hG (i₀, k)
          (Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩)
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hD i₀) (not_le.mp hk))
    · by_cases hk : k ≤ D
      · exact Finset.gcd_dvd (f := fun t : Fin (n + 1) × ℕ => (a₁ t.1).coeff t.2) (b := (i, k))
          (Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_range.mpr (by omega)⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hD i) (not_le.mp hk))]
        exact dvd_zero _
  have hCdvd : ∀ i, C G ∣ a₁ i := fun i => (C_dvd_iff_dvd_coeff G (a₁ i)).mpr (hGdvd i)
  choose a ha using hCdvd
  refine ⟨a, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hdiv : G * ℓ ∣ G := by
      refine hGmax _ fun i k => ?_
      rw [ha i, coeff_C_mul]
      exact mul_dvd_mul_left G (hall i k)
    have h1 : (ℓ : ℤ) ∣ 1 := (mul_dvd_mul_iff_left hG0).mp (by simpa using hdiv)
    have := Int.eq_one_of_dvd_one (Int.natCast_nonneg ℓ) h1
    exact hℓ (by exact_mod_cast this)
  · have h1 : (G : modularFunctionFieldFullC ℚ M) * ∑ i, aeval (jF M) (a i) * m i = 0 := by
      rw [Finset.mul_sum, ← hrel₁]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ha i, map_mul, aeval_C, algebraMap_int_eq, eq_intCast, mul_assoc]
    exact (mul_eq_zero.mp h1).resolve_left (Int.cast_ne_zero.mpr hG0)

end Steps

private theorem exists_int_relation [NeZero M] (ℓ : ℕ) (hℓ : ℓ ≠ 1)
    (m : Fin (dedekindPsi M + 1) → modularFunctionFieldFullC ℚ M) :
    ∃ a : Fin (dedekindPsi M + 1) → ℤ[X],
      (∃ i k, ¬ (ℓ : ℤ) ∣ (a i).coeff k) ∧ ∑ i, aeval (jF M) (a i) * m i = 0 := by
  haveI : Module.Finite (KJ M) (modularFunctionFieldFullC ℚ M) :=
    Module.finite_of_finrank_pos (by rw [finrank_full]; exact dedekindPsi_pos M)
  have hdep : ¬ LinearIndependent (KJ M) m :=
    fun h => by
      have := h.fintype_card_le_finrank
      rw [finrank_full, Fintype.card_fin] at this
      omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨P, hP0, hP⟩ := exists_rat_poly_relation m g hg i₀ hi₀
  obtain ⟨a₁, ha₁, ha₁rel⟩ := exists_int_poly_relation m P i₀ hP0 hP
  exact exists_coprime_int_poly_relation m ℓ hℓ a₁ i₀ ha₁ ha₁rel

end Relations

section Rank

open Submodule

section RankLe

variable {D : Type*} [CommRing D] [IsDomain D] {A : Type*} [AddCommGroup A] [Module D A]

private theorem exists_smul_mem_span_of_maximal {W : Type*} [Fintype W] (v : W → A) (I : Set W)
    (hImax : ∀ w ∉ I, ∃ a : D, a ≠ 0 ∧ a • v w ∈ span D (v '' I)) :
    ∃ d : D, d ≠ 0 ∧ ∀ x ∈ span D (Set.range v), d • x ∈ span D (v '' I) := by
  classical
  have hw : ∀ w, ∃ a : D, a ≠ 0 ∧ a • v w ∈ span D (v '' I) := by
    intro w
    by_cases h : w ∈ I
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact subset_span ⟨w, h, rfl⟩⟩
    · exact hImax w h
  choose a ha hav using hw
  refine ⟨∏ w, a w, Finset.prod_ne_zero_iff.mpr fun w _ => ha w, fun x hx => ?_⟩
  induction hx using span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    rw [← Finset.prod_erase_mul Finset.univ a (Finset.mem_univ w), mul_smul]
    exact smul_mem _ _ (hav w)
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact smul_mem _ _ hy

private theorem rank_le_of_forall_dependent {ι : Type*} (t : ι → A) (ht : span D (Set.range t) = ⊤) (n : ℕ)
    (hdep : ∀ m : Fin (n + 1) → ι, Function.Injective m → ¬ LinearIndependent D (t ∘ m)) :
    Module.rank D A ≤ n := by
  classical
  apply _root_.rank_le
  intro s hs

  obtain ⟨W, hWt, hsW⟩ : ∃ W : Finset A, (↑W ⊆ Set.range t) ∧ ∀ x ∈ s, (x : A) ∈ span D (W : Set A) := by
    have hx : ∀ x : A, ∃ T : Finset A, ↑T ⊆ Set.range t ∧ x ∈ span D (T : Set A) := fun x =>
      mem_span_finite_of_mem_span (by rw [ht]; exact mem_top)
    choose T hT hxT using hx
    refine ⟨s.biUnion T, ?_, fun x hxs => ?_⟩
    · intro y hy
      simp only [Finset.coe_biUnion, Set.mem_iUnion] at hy
      obtain ⟨x, -, hy⟩ := hy
      exact hT x hy
    · exact span_mono (by
        intro y hy
        simp only [Finset.coe_biUnion, Set.mem_iUnion]
        exact ⟨x, hxs, hy⟩) (hxT x)

  obtain ⟨I, hI, hImax⟩ := exists_maximal_linearIndepOn D (fun w : W => (w : A))
  have hIcard : Fintype.card I ≤ n := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨e⟩ : Nonempty (Fin (n + 1) ↪ I) := Function.Embedding.nonempty_of_card_le (by simpa using hlt)
    have hmem : ∀ i, (((e i : I) : W) : A) ∈ Set.range t := fun i => hWt ((e i : I) : W).2
    choose m hm using hmem
    have hinj : Function.Injective m := by
      intro i i' h
      have : (((e i : I) : W) : A) = (((e i' : I) : W) : A) := by rw [← hm i, ← hm i', h]
      exact e.injective (Subtype.ext (Subtype.ext this))
    apply hdep m hinj
    have hcomp : t ∘ m = (fun w : I => ((w : W) : A)) ∘ e := by
      ext i
      simp [hm i]
    rw [hcomp]
    exact hI.comp e e.injective

  obtain ⟨d, hd0, hd⟩ := exists_smul_mem_span_of_maximal (fun w : W => (w : A)) I hImax
  have hrange : Set.range (fun w : W => (w : A)) = (W : Set A) := by
    ext y
    simp

  have hind : LinearIndependent D (fun x : s => d • (x : A)) := by
    rw [Fintype.linearIndependent_iff] at hs ⊢
    intro g hg i
    have h1 : ∑ i, (g i * d) • ((i : s) : A) = 0 := by
      rw [← hg]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]
    exact (mul_eq_zero.mp (hs _ h1 i)).resolve_right hd0
  have himg : ((fun w : W => (w : A)) '' I) = Set.range (fun w : I => ((w : W) : A)) := Set.image_eq_range _ _
  have hle : Set.range (fun x : s => d • (x : A)) ≤ span D (Set.range fun w : I => ((w : W) : A)) := by
    rintro _ ⟨x, rfl⟩
    rw [← himg]
    exact hd _ (by rw [hrange]; exact hsW x x.2)
  have h1 := linearIndependent_le_span_aux' _ hind _ hle
  rw [Fintype.card_coe] at h1
  exact h1.trans ((Fintype.card_range_le _).trans hIcard)

end RankLe

section Squeeze

universe u v w

variable {D : Type u} [CommRing D] [IsDomain D] {A : Type v} {B : Type w} [AddCommGroup A] [Module D A]
  [AddCommGroup B] [Module D B]

private theorem exists_smul_eq_zero_of_mem_ker (π : A →ₗ[D] B) (hπ : Function.Surjective π) (n : ℕ)
    (hA : Module.rank D A ≤ n) (hB : (n : Cardinal) ≤ Module.rank D B) {x : A} (hx : x ∈ LinearMap.ker π) :
    ∃ a : D, a ≠ 0 ∧ a • x = 0 := by
  have hker : Module.rank D (LinearMap.ker π) = 0 := by
    have h := LinearMap.lift_rank_range_add_rank_ker π
    rw [LinearMap.range_eq_top.mpr hπ, rank_top] at h

    by_contra hne
    have h1 : (1 : Cardinal) ≤ Cardinal.lift.{w} (Module.rank D (LinearMap.ker π)) :=
      Cardinal.one_le_iff_ne_zero.mpr (by rwa [Ne, Cardinal.lift_eq_zero])
    have hA' : Cardinal.lift.{w} (Module.rank D A) ≤ n := by
      rw [← Cardinal.lift_natCast.{w, v} n, Cardinal.lift_le]; exact hA
    have hB' : (n : Cardinal) ≤ Cardinal.lift.{v} (Module.rank D B) := by
      rw [← Cardinal.lift_natCast.{v, w} n, Cardinal.lift_le]; exact hB
    have h2 : (n : Cardinal) + 1 ≤ n := by
      calc (n : Cardinal) + 1 ≤ Cardinal.lift.{v} (Module.rank D B) + Cardinal.lift.{w} (Module.rank D (LinearMap.ker π)) :=
            add_le_add hB' h1
        _ = Cardinal.lift.{w} (Module.rank D A) := h
        _ ≤ n := hA'
    have h3 : ((n + 1 : ℕ) : Cardinal.{max v w}) ≤ ((n : ℕ) : Cardinal.{max v w}) := by exact_mod_cast h2
    exact absurd (Nat.cast_le.mp h3) (by omega)
  obtain ⟨a, ha, hax⟩ := rank_eq_zero_iff.mp hker ⟨x, hx⟩
  exact ⟨a, ha, by simpa using congrArg Subtype.val hax⟩

end Squeeze

section TensorReduction

universe u v

variable {k : Type u} [Field k] (ℓ : ℕ) [CharP k ℓ]
variable {R : Type v} [CommRing R]
variable {L : Type u} [CommRing L] [Algebra k L]

private theorem exists_aeval_mul_eq_zero_of_redMap_eq_zero (ρ : R →ₐ[ℤ] L) (jR : R) (n : ℕ)
    (hrel : ∀ m : Fin (n + 1) → R, ∃ a : Fin (n + 1) → ℤ[X],
      (∃ i c, ¬ (ℓ : ℤ) ∣ (a i).coeff c) ∧ ∑ i, aeval jR (a i) * m i = 0)
    (hw : ∃ w : Fin n → L, (∀ t, w t ∈ Algebra.adjoin k (Set.range ρ)) ∧
      ∀ f : Fin n → k[X], ∑ t, aeval (ρ jR) (f t) * w t = 0 → ∀ t, f t = 0)
    (x : k ⊗[ℤ] R) (hx : redMap ρ x = 0) :
    ∃ f : k[X], f ≠ 0 ∧ aeval ((1 : k) ⊗ₜ[ℤ] jR) f * x = 0 := by
  classical

  let A := k ⊗[ℤ] R
  let φA : k[X] →ₐ[k] A := aeval ((1 : k) ⊗ₜ[ℤ] jR)
  letI modA : Module k[X] A := φA.toRingHom.toModule
  have smulA : ∀ (f : k[X]) (a : A), f • a = φA f * a := fun _ _ => rfl
  let B : Subalgebra k L := (redMap ρ).range
  have hjB : ρ jR ∈ B := ⟨(1 : k) ⊗ₜ jR, redMap_one_tmul ρ jR⟩
  let φB : k[X] →ₐ[k] B := aeval (⟨ρ jR, hjB⟩ : B)
  letI modB : Module k[X] B := φB.toRingHom.toModule
  have smulB : ∀ (f : k[X]) (b : B), f • b = φB f * b := fun _ _ => rfl
  have coe_φB : ∀ f : k[X], ((φB f : B) : L) = aeval (ρ jR) f := fun f =>
    (aeval_algHom_apply B.val (⟨ρ jR, hjB⟩ : B) f).symm

  have hπφ : ∀ f : k[X], redMap ρ (φA f) = aeval (ρ jR) f := fun f => by
    rw [← aeval_algHom_apply, redMap_one_tmul]
  let π : A →ₗ[k[X]] B :=
    { toFun := fun a => ⟨redMap ρ a, a, rfl⟩
      map_add' := fun a b => Subtype.ext (map_add _ a b)
      map_smul' := fun f a => Subtype.ext (by
        rw [RingHom.id_apply, smulA, smulB, Subalgebra.coe_mul, coe_φB, ← hπφ f, ← map_mul]) }
  have hπsurj : Function.Surjective π := by
    rintro ⟨y, a, rfl⟩
    exact ⟨a, rfl⟩

  have hA : Module.rank k[X] A ≤ n := by
    refine rank_le_of_forall_dependent (D := k[X]) (fun r : R => ((1 : k) ⊗ₜ[ℤ] r : A)) ?_ n ?_
    · rw [eq_top_iff]
      rintro x -
      induction x using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul c r =>
        have h1 : (c ⊗ₜ[ℤ] r : A) = (C c : k[X]) • ((1 : k) ⊗ₜ[ℤ] r : A) := by
          rw [smulA, show φA (C c) = algebraMap k A c from aeval_C _ _, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [h1]
        exact smul_mem _ _ (subset_span ⟨r, rfl⟩)
      | add x y hx hy => exact add_mem hx hy
    · intro m _ hind
      obtain ⟨a, ⟨i₀, c₀, hi₀⟩, hsum⟩ := hrel m
      apply Fintype.not_linearIndependent_iff.mpr ?_ hind
      refine ⟨fun i => (a i).map (Int.castRingHom k), ?_, i₀, ?_⟩
      · have h1 : ∀ i, ((a i).map (Int.castRingHom k)) • ((1 : k) ⊗ₜ[ℤ] m i : A)
            = (1 : k) ⊗ₜ[ℤ] (aeval jR (a i) * m i) := by
          intro i
          rw [smulA]
          have h2 : φA ((a i).map (Int.castRingHom k)) = (1 : k) ⊗ₜ[ℤ] aeval jR (a i) := by
            rw [← algebraMap_int_eq, aeval_map_algebraMap]
            change aeval ((Algebra.TensorProduct.includeRight : R →ₐ[ℤ] A) jR) (a i) = _
            rw [aeval_algHom_apply, Algebra.TensorProduct.includeRight_apply]
          rw [h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        have h3 : ∀ i, ((fun r : R => ((1 : k) ⊗ₜ[ℤ] r : A)) ∘ m) i = (1 : k) ⊗ₜ[ℤ] m i := fun i => rfl
        simp_rw [h3, h1]
        rw [← TensorProduct.tmul_sum, hsum, TensorProduct.tmul_zero]
      · intro h0
        apply hi₀
        rw [← CharP.intCast_eq_zero_iff k ℓ]
        have := congrArg (fun q : k[X] => q.coeff c₀) h0
        simpa [Polynomial.coeff_map] using this

  have hB : (n : Cardinal) ≤ Module.rank k[X] B := by
    obtain ⟨w, hwB, hwind⟩ := hw
    have hle : Algebra.adjoin k (Set.range ρ) ≤ B := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨r, rfl⟩
      exact ⟨(1 : k) ⊗ₜ r, redMap_one_tmul ρ r⟩
    have hwB' : ∀ t, w t ∈ B := fun t => hle (hwB t)
    have hind : LinearIndependent k[X] (fun t => (⟨w t, hwB' t⟩ : B)) := by
      rw [Fintype.linearIndependent_iff]
      intro f hf t
      apply hwind f ?_ t
      have := congrArg (fun b : B => (b : L)) hf
      simp only [smulB, Subalgebra.coe_zero] at this
      rw [← this, ← Subalgebra.val_apply, map_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [Subalgebra.val_apply, Subalgebra.coe_mul, coe_φB]
    have := hind.cardinal_lift_le_rank
    simpa using this

  have hxker : x ∈ LinearMap.ker π := by
    rw [LinearMap.mem_ker]
    exact Subtype.ext hx
  obtain ⟨f, hf0, hfx⟩ := exists_smul_eq_zero_of_mem_ker π hπsurj n hA hB hxker
  exact ⟨f, hf0, by rw [← smulA]; exact hfx⟩

end TensorReduction

end Rank

section Independent

variable (k : Type*) [Field k] (M : ℕ) [NeZero M]

private def gensC : Set (LaurentSeries k) := divisorExpansionsC k M

private abbrev jFk : modularFunctionFieldFullC k M := ⟨jqModC k, jqModC_mem_full k M⟩

private abbrev KJk : IntermediateField k (modularFunctionFieldFullC k M) :=
  IntermediateField.adjoin k ({jFk k M} : Set (modularFunctionFieldFullC k M))

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance algKJk : Algebra (KJk k M) (modularFunctionFieldFullC k M) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance modKJk : Module (KJk k M) (modularFunctionFieldFullC k M) := inferInstance

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance towKJk : IsScalarTower k (KJk k M) (modularFunctionFieldFullC k M) := inferInstance

private scoped instance freeKJk : Module.Free (KJk k M) (modularFunctionFieldFullC k M) := Module.Free.of_divisionRing _ _

private theorem exists_independent (hMk : (M : k) ≠ 0) :
    ∃ w : Fin (dedekindPsi M) → LaurentSeries k,
      (∀ t, w t ∈ Algebra.adjoin k (gensC k M)) ∧
        ∀ f : Fin (dedekindPsi M) → k[X], ∑ t, aeval (jqModC k) (f t) * w t = 0 → ∀ t, f t = 0 := by
  classical
  let F := modularFunctionFieldFullC k M
  have hfin : Module.finrank (KJk k M) F = dedekindPsi M :=
    finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi k M hMk
  have hpos : 0 < dedekindPsi M := by
    unfold dedekindPsi
    have h1 : 1 ∈ M.divisors.filter Squarefree := by simp [Nat.mem_divisors, NeZero.ne M]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1)
    simpa using Nat.pos_of_ne_zero (NeZero.ne M)
  haveI : Module.Finite (KJk k M) F := Module.finite_of_finrank_pos (by rw [hfin]; exact hpos)
  let b := Module.finBasisOfFinrankEq (KJk k M) F hfin

  have hb : ∀ t, ∃ r s : LaurentSeries k, r ∈ Algebra.adjoin k (gensC k M) ∧ s ∈ Algebra.adjoin k (gensC k M) ∧
      s ≠ 0 ∧ ((b t : F) : LaurentSeries k) * s = r := by
    intro t
    obtain ⟨r, hr, s, hs, hrs⟩ := (IntermediateField.mem_adjoin_iff_div (F := k) (S := gensC k M)).mp (b t).2
    have hs0 : s ≠ 0 := by
      intro h0
      apply b.ne_zero t
      apply Subtype.ext
      change ((b t : F) : LaurentSeries k) = 0
      rw [hrs, h0, div_zero]
    exact ⟨r, s, hr, hs, hs0, by rw [hrs, div_mul_cancel₀ _ hs0]⟩
  choose r s hr hs hs0 hbrs using hb
  refine ⟨fun t => r t * ∏ t' ∈ Finset.univ.erase t, s t', fun t => ?_, fun f hf => ?_⟩
  · exact mul_mem (hr t) (prod_mem fun t' _ => hs t')
  ·
    have hS0 : (∏ t', s t') ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t' _ => hs0 t'
    have hw : ∀ t, r t * ∏ t' ∈ Finset.univ.erase t, s t' = ((b t : F) : LaurentSeries k) * ∏ t', s t' := by
      intro t
      rw [← hbrs t, mul_assoc, Finset.mul_prod_erase Finset.univ s (Finset.mem_univ t)]
    simp_rw [hw, ← mul_assoc, ← Finset.sum_mul] at hf
    have hf' : ∑ t, aeval (jqModC k) (f t) * ((b t : F) : LaurentSeries k) = 0 :=
      (mul_eq_zero.mp hf).resolve_right hS0

    have hc : ∀ t, aeval (jFk k M) (f t) ∈ KJk k M := fun t =>
      IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    have hcoe : ∀ t, ((aeval (jFk k M) (f t) : F) : LaurentSeries k) = aeval (jqModC k) (f t) := fun t =>
      (aeval_algHom_apply (modularFunctionFieldFullC k M).val (jFk k M) (f t)).symm
    have hrel : ∑ t, (⟨aeval (jFk k M) (f t), hc t⟩ : KJk k M) • b t = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, ← hf', AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [IntermediateField.smul_def, smul_eq_mul, MulMemClass.coe_mul]
      exact congrArg (· * _) (hcoe t)
    have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent _ hrel
    intro t
    have h1 : aeval (jFk k M) (f t) = 0 := congrArg Subtype.val (h0 t)
    have h2 : aeval (jqModC k) (f t) = 0 := by
      rw [← hcoe t, h1]
      rfl
    exact (transcendental_iff.mp (transcendental_jqModC k)) _ h2

end Independent

section Assembly

variable (N p : ℕ) [NeZero N] [NeZero p]
variable (σ : modularFunctionFieldFull (N * p) ≃ₐ[ℚ] modularFunctionFieldFull (N * p))
  (hσ : IsAtkinLehnerAutFull N p σ) (hp : p.Prime)
variable (K : Type*) [Field K]

omit [NeZero N] [NeZero p] in
private theorem ringHom_aeval_int {T U : Type*} [CommRing T] [Ring U] [Algebra ℤ T] [Algebra ℤ U] (ψ : T →+* U)
    (x : T) (a : ℤ[X]) : ψ (aeval x a) = aeval (ψ x) a := by
  rw [map_aeval_eq_aeval_map (φ := RingHom.id ℤ) (RingHom.ext_int _ _) a x, Polynomial.map_id]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_int_relation_genRing (ℓ : ℕ) (hℓ : ℓ ≠ 1) (m : Fin (dedekindPsi (N * p) + 1) → genRing N p) :
    ∃ a : Fin (dedekindPsi (N * p) + 1) → ℤ[X],
      (∃ i c, ¬ (ℓ : ℤ) ∣ (a i).coeff c) ∧ ∑ i, aeval (jR N p) (a i) * m i = 0 := by
  obtain ⟨a, ha, hrel⟩ := exists_int_relation (N * p) ℓ hℓ (fun i => (m i : modularFunctionFieldFull (N * p)))
  refine ⟨a, ha, θ_injective N p ?_⟩
  have h1 := congrArg (fun y : modularFunctionFieldFullC ℚ (N * p) => (y : LaurentSeries ℚ)) hrel
  simp only [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] at h1
  rw [RingHom.map_zero, map_sum (θ N p), ← h1]
  have hj : (((jR N p : genRing N p) : modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) = jqModC ℚ := by
    rw [← θ_apply]
    show θ N p ⟨gen N p 1 (one_dvd _), gen_mem_genRing N p 1 (one_dvd _)⟩ = _
    rw [θ_gen, qExpand_one_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mul, ringHom_aeval_int, θ_apply, θ_apply, hj]
  congr 1
  change _ = SubringClass.subtype (modularFunctionFieldFullC ℚ (N * p)) (aeval (jF (N * p)) (a i))
  rw [ringHom_aeval_int]
  rfl

private theorem torsion (hNK : (N : K) ≠ 0) (hpK : (p : K) ≠ 0) (x : K ⊗[ℤ] genRing N p)
    (hx : redMap (ρₐ N p K) x = 0) : ∃ f : K[X], f ≠ 0 ∧ aeval ((1 : K) ⊗ₜ[ℤ] jR N p) f * x = 0 := by
  haveI := ringChar.charP K
  refine exists_aeval_mul_eq_zero_of_redMap_eq_zero (ringChar K) (ρₐ N p K) (jR N p) (dedekindPsi (N * p))
    (exists_int_relation_genRing N p (ringChar K) CharP.ringChar_ne_one) ?_ x hx
  have hMk : ((N * p : ℕ) : K) ≠ 0 := by push_cast; exact mul_ne_zero hNK hpK
  obtain ⟨w, hw, hind⟩ := exists_independent K (N * p) hMk
  refine ⟨w, fun t => Algebra.adjoin_mono ?_ (hw t), ?_⟩
  · rintro _ ⟨e, _, he, rfl⟩
    exact ⟨⟨gen N p e he, gen_mem_genRing N p e he⟩, by rw [ρₐ_apply, ρ_gen]⟩
  · intro f hf
    rw [ρₐ_apply, ρ_jR] at hf
    exact hind f hf

variable (hNK : (N : K) ≠ 0) (hpK : (p : K) ≠ 0)

open scoped IntermediateField.algebraAdjoinAdjoin in

private def toggle : IntermediateField.adjoin K (divisorExpansionsC K (N * p))
    ≃ₐ[K] IntermediateField.adjoin K (divisorExpansionsC K (N * p)) :=
  IsFractionRing.algEquivOfAlgEquiv (σC N p σ hσ hp K (torsion N p K hNK hpK))

open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem coe_toggle_gen (e : ℕ) [NeZero e] (he : e ∣ N * p)
    (hmem : qExpand K e (jqModC K) ∈ IntermediateField.adjoin K (divisorExpansionsC K (N * p))) :
    ((toggle N p σ hσ hp K hNK hpK ⟨qExpand K e (jqModC K), hmem⟩ :
        IntermediateField.adjoin K (divisorExpansionsC K (N * p))) : LaurentSeries K)
      = ρ N p K (σR N p σ hσ hp ⟨gen N p e he, gen_mem_genRing N p e he⟩) := by
  have hmem' : qExpand K e (jqModC K) ∈ Algebra.adjoin K (divisorExpansionsC K (N * p)) :=
    Algebra.subset_adjoin ⟨e, inferInstance, he, rfl⟩
  have h1 : (⟨qExpand K e (jqModC K), hmem⟩ : IntermediateField.adjoin K (divisorExpansionsC K (N * p)))
      = algebraMap (Algebra.adjoin K (divisorExpansionsC K (N * p))) _ ⟨qExpand K e (jqModC K), hmem'⟩ :=
    Subtype.ext rfl
  rw [h1, toggle, IsFractionRing.algEquivOfAlgEquiv_algebraMap, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap,
    coe_σC_gen]

private theorem toggle_gen_of_dvd (d : ℕ) [NeZero d] (hd : d ∣ N) :
    toggle N p σ hσ hp K hNK hpK ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * p) (Dvd.dvd.mul_right hd p)⟩
        = ⟨qExpand K (d * p) (jqModC K), jqModCd_mem_full K (N * p) (Nat.mul_dvd_mul_right hd p)⟩
      ∧ toggle N p σ hσ hp K hNK hpK
          ⟨qExpand K (d * p) (jqModC K), jqModCd_mem_full K (N * p) (Nat.mul_dvd_mul_right hd p)⟩
        = ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * p) (Dvd.dvd.mul_right hd p)⟩ := by
  constructor
  · apply Subtype.ext
    rw [coe_toggle_gen N p σ hσ hp K hNK hpK d (Dvd.dvd.mul_right hd p), σR_apply,
      (genRingAut_gen_of_dvd N p σ hσ hp d hd).1, ρ_gen]
  · apply Subtype.ext
    rw [coe_toggle_gen N p σ hσ hp K hNK hpK (d * p) (Nat.mul_dvd_mul_right hd p), σR_apply,
      (genRingAut_gen_of_dvd N p σ hσ hp d hd).2, ρ_gen]

end Assembly

end AtkinLehnerC
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd.AtkinLehnerC"

open AtkinLehnerC in
theorem solution (K : Type*) [Field K]
    (N p : ℕ) [NeZero N] [NeZero p] (hp : p.Prime) (hpN : ¬ p ∣ N) (hNK : (N : K) ≠ 0) (hpK : (p : K) ≠ 0) :
    ∃ σ : modularFunctionFieldFullC K (N * p) ≃ₐ[K] modularFunctionFieldFullC K (N * p),
      ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
        σ ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * p) (Dvd.dvd.mul_right hd p)⟩
            = ⟨qExpand K (d * p) (jqModC K), jqModCd_mem_full K (N * p) (Nat.mul_dvd_mul_right hd p)⟩
          ∧ σ ⟨qExpand K (d * p) (jqModC K), jqModCd_mem_full K (N * p) (Nat.mul_dvd_mul_right hd p)⟩
            = ⟨qExpand K d (jqModC K), jqModCd_mem_full K (N * p) (Dvd.dvd.mul_right hd p)⟩ := by
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p hp hpN
  exact ⟨toggle N p σ hσ hp K hNK hpK, fun d _ hd => toggle_gen_of_dvd N p σ hσ hp K hNK hpK d hd⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd.AtkinLehnerC"

end S_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd (solution)
