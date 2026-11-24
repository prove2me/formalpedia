-- Prove2me | solution 1 for GlobalTheory.PolyNorm.norm_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:13.543591+00:00
-- url     : https://prove2.me/submissions/de27fb62-22c6-40b7-b44f-8a32aeb8ff48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (U : Matrix (Fin m) (Fin m) ℤ_[l])
    (N : ℤ[X] → ℚ) (Good : ℤ[X] → Prop)
    (hp : ∀ F : ℤ[X], ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ))
    (hG : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t))
    (hn : ∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) (F : ℤ[X]) :
    ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖ := by
  obtain ⟨p, hp⟩ := hp F
  have t0 : Filter.Tendsto (fun k : ℕ => (l : ℤ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt))
  have c1 : Continuous fun x : ℤ_[l] => ‖(p.map (Rat.castHom ℚ_[l])).eval (x : ℚ_[l])‖ :=
    ((p.map (Rat.castHom ℚ_[l])).continuous.comp continuous_subtype_val).norm
  have c2 : Continuous fun x : ℤ_[l] =>
      ‖(Polynomial.aeval U F + x • (1 : Matrix (Fin m) (Fin m) ℤ_[l])).det‖ :=
    ((continuous_const.add (continuous_id.smul continuous_const)).matrix_det).norm
  have e1 : ∀ t : ℕ, ((N (F + t) : ℚ) : ℚ_[l]) =
      (p.map (Rat.castHom ℚ_[l])).eval (((t : ℤ_[l])) : ℚ_[l]) := fun t => by
    rw [hp, PadicInt.coe_natCast, ← map_natCast (Rat.castHom ℚ_[l]), eval_map, eval₂_at_apply]
    rfl
  have e2 : ∀ t : ℕ, Polynomial.aeval U (F + (t : ℤ[X])) =
      Polynomial.aeval U F + (t : ℤ_[l]) • (1 : Matrix (Fin m) (Fin m) ℤ_[l]) := fun t => by
    rw [map_add, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_one]
  have h := tendsto_nhds_unique_of_eventuallyEq ((c1.tendsto 0).comp t0) ((c2.tendsto 0).comp t0)
    (((tendsto_pow_atTop_atTop_of_one_lt hl.out.one_lt).eventually (hG F)).mono fun k hk => by
      have := hn _ hk
      rw [e1, e2] at this
      simpa using this)
  have := e1 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this, h]
  simp
end GlobalTheory.PolyNorm
