-- Prove2me | solution 1 for ModularCurve.coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/648470de-233e-5c14-9716-ab2640e4f12c

import Mathlib
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve

namespace ALLegs

theorem dvd_mul_prime_cases {N₀ q e : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N₀) (he : e ∣ N₀ * q) :
    e ∣ N₀ ∨ ∃ d, d ∣ N₀ ∧ e = d * q := by
  obtain ⟨e₁, e₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.mp he
  rcases (Nat.dvd_prime hq).mp h₂ with rfl | rfl
  · left; simpa using h₁
  · right; exact ⟨e₁, h₁, rfl⟩

theorem ringHom_ext_full {N : ℕ} [NeZero N] {L : Type*} [DivisionRing L] [CharZero L]
    {g₁ g₂ : ↥(modularFunctionFieldFull N) →+* L}
    (h : ∀ (e : ℕ) (_ : NeZero e) (he : e ∣ N), g₁ ⟨qExpand ℚ e jq, jqd_mem_full N he⟩ = g₂ ⟨qExpand ℚ e jq, jqd_mem_full N he⟩) :
    g₁ = g₂ := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨e, inst, he, rfl⟩ := hx
    exact h e inst he
  | algebraMap r =>
    have e1 : (⟨algebraMap ℚ (LaurentSeries ℚ) r, IntermediateField.algebraMap_mem _ r⟩ : ↥(modularFunctionFieldFull N)) =
        ((r : ℚ) : ↥(modularFunctionFieldFull N)) := by
      apply Subtype.ext
      simp [eq_ratCast]
    rw [e1, map_ratCast, map_ratCast]
  | add x y hx hy ihx ihy =>
    have e1 : (⟨x + y, IntermediateField.add_mem _ hx hy⟩ : ↥(modularFunctionFieldFull N)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e1, map_add, map_add, ihx, ihy]
  | inv x hx ihx =>
    have e1 : (⟨x⁻¹, IntermediateField.inv_mem _ hx⟩ : ↥(modularFunctionFieldFull N)) = (⟨x, hx⟩ : ↥(modularFunctionFieldFull N))⁻¹ := rfl
    rw [e1, map_inv₀, map_inv₀, ihx]
  | mul x y hx hy ihx ihy =>
    have e1 : (⟨x * y, IntermediateField.mul_mem _ hx hy⟩ : ↥(modularFunctionFieldFull N)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e1, map_mul, map_mul, ihx, ihy]

end ALLegs

open ALLegs in
theorem solution
    (N₀ q ℓ : ℕ) [NeZero N₀] [NeZero ℓ] [Fact q.Prime] (hq : ¬ q ∣ N₀ * ℓ)
    (f : ↥(modularFunctionFieldFull (N₀ * q))) (f' : ↥(modularFunctionFieldFull (N₀ * ℓ * q)))
    (hf : ((f' : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) = ((f : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) :
    ((atkinLehnerInvolutionFull (N₀ * ℓ) q f' : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
      ((atkinLehnerInvolutionFull N₀ q f : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) := by
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  have hq0 : ¬ q ∣ N₀ := fun h => hq (h.mul_right ℓ)
  have hw : IsAtkinLehnerAutFull N₀ q (atkinLehnerInvolutionFull N₀ q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N₀ q (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N₀ q hqp hq0)
  have hw' : IsAtkinLehnerAutFull (N₀ * ℓ) q (atkinLehnerInvolutionFull (N₀ * ℓ) q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull (N₀ * ℓ) q (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd (N₀ * ℓ) q hqp hq)

  have hle : modularFunctionFieldFull (N₀ * q) ≤ modularFunctionFieldFull (N₀ * ℓ * q) :=
    full_degeneracy_le ⟨ℓ, by ring⟩
  let ι : ↥(modularFunctionFieldFull (N₀ * q)) →+* ↥(modularFunctionFieldFull (N₀ * ℓ * q)) :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf' : f' = ι f := Subtype.ext (by rw [hf]; rfl)
  rw [hf']

  set w := atkinLehnerInvolutionFull N₀ q with hwdef
  set w' := atkinLehnerInvolutionFull (N₀ * ℓ) q with hw'def
  let g₁ : ↥(modularFunctionFieldFull (N₀ * q)) →+* LaurentSeries ℚ :=
    (modularFunctionFieldFull (N₀ * q)).toSubfield.subtype.comp w.toRingEquiv.toRingHom
  let g₂ : ↥(modularFunctionFieldFull (N₀ * q)) →+* LaurentSeries ℚ :=
    (modularFunctionFieldFull (N₀ * ℓ * q)).toSubfield.subtype.comp (w'.toRingEquiv.toRingHom.comp ι)
  suffices hg : g₁ = g₂ by
    have := congrArg (fun g => g f) hg
    exact this.symm
  haveI : CharZero (LaurentSeries ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ (LaurentSeries ℚ)).injective
  apply ringHom_ext_full
  intro e _ he

  have hιe : ∀ (d : ℕ) [NeZero d] (hd : d ∣ N₀ * q) (hd' : d ∣ N₀ * ℓ * q),
      ι ⟨qExpand ℚ d jq, jqd_mem_full (N₀ * q) hd⟩ = ⟨qExpand ℚ d jq, jqd_mem_full (N₀ * ℓ * q) hd'⟩ :=
    fun d _ hd hd' => Subtype.ext rfl
  change ((w ⟨qExpand ℚ e jq, jqd_mem_full (N₀ * q) he⟩ : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
    ((w' (ι ⟨qExpand ℚ e jq, jqd_mem_full (N₀ * q) he⟩) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ)
  rcases dvd_mul_prime_cases hqp hq0 he with hd | ⟨d, hd, rfl⟩
  ·
    have h1 := (hw e ‹_› hd).1
    have h2 := (hw' e ‹_› (hd.trans (dvd_mul_right N₀ ℓ))).1
    have k1 : (⟨qExpand ℚ e jq, jqd_mem_full (N₀ * q) he⟩ : ↥(modularFunctionFieldFull (N₀ * q))) =
        ⟨qExpand ℚ e jq, jqd_mem_full (N₀ * q) (Dvd.dvd.mul_right hd q)⟩ := rfl
    rw [k1, h1, hιe e (Dvd.dvd.mul_right hd q) (Dvd.dvd.mul_right (hd.trans (dvd_mul_right N₀ ℓ)) q), h2]
  ·
    haveI : NeZero d := ⟨fun h => by simp [h] at *⟩
    have h1 := (hw d ‹_› hd).2
    have h2 := (hw' d ‹_› (hd.trans (dvd_mul_right N₀ ℓ))).2
    have k1 : (⟨qExpand ℚ (d * q) jq, jqd_mem_full (N₀ * q) he⟩ : ↥(modularFunctionFieldFull (N₀ * q))) =
        ⟨qExpand ℚ (d * q) jq, jqd_mem_full (N₀ * q) (Nat.mul_dvd_mul_right hd q)⟩ := rfl
    rw [k1, h1, hιe (d * q) (Nat.mul_dvd_mul_right hd q) (Nat.mul_dvd_mul_right (hd.trans (dvd_mul_right N₀ ℓ)) q), h2]

end S_ModularCurve_coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq
end P2MW
export P2MW.S_ModularCurve_coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq (solution)
