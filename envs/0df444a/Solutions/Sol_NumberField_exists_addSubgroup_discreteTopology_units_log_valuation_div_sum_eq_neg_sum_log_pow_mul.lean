-- Prove2me | solution 1 for NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/419124a4-b1a7-51e9-9124-348491cb9678

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace R1L9

def scale {r d : ℕ} (f : Fin d → ℤ) : ((Fin r → ℝ) × (Fin d → ℤ)) →+ ((Fin r → ℝ) × (Fin d → ℤ)) where
  toFun γ := (γ.1, fun j => f j * γ.2 j)
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [mul_add]

theorem scale_apply {r d : ℕ} (f : Fin d → ℤ) (γ : (Fin r → ℝ) × (Fin d → ℤ)) :
    scale f γ = (γ.1, fun j => f j * γ.2 j) := rfl

theorem scale_injective {r d : ℕ} (f : Fin d → ℤ) (hf : ∀ j, f j ≠ 0) : Function.Injective (scale (r := r) f) := by
  intro a b h
  rw [scale_apply, scale_apply, Prod.mk.injEq] at h
  refine Prod.ext h.1 (funext fun j => ?_)
  have := congrFun h.2 j
  exact mul_left_cancel₀ (hf j) this

theorem continuous_scale {r d : ℕ} (f : Fin d → ℤ) : Continuous (scale (r := r) f) :=
  continuous_fst.prodMk
    ((continuous_of_discreteTopology (f := fun k : Fin d → ℤ => fun j => f j * k j)).comp continuous_snd)

end R1L9

theorem solution
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (f : HeightOneSpectrum (𝓞 K) → ℕ) (hf : ∀ v ∈ T, 0 < f v) :
    ∃ (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
      (Log : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)),
      (∀ u : Kˣ, Log u =
        (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
            Real.log (((Fintype.equivFin (InfinitePlace K)).symm i) (u : K)),
          fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u))) ∧
      (∀ u u' : Kˣ, Log (u * u') = Log u + Log u') ∧
      (∀ γ, γ ∈ Λ ↔ ∃ u : Kˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧
          Log u = (γ.1, fun j => (f (T.equivFin.symm j).1 : ℤ) * γ.2 j)) ∧
      DiscreteTopology Λ ∧
      (∀ γ ∈ Λ, ∑ i, γ.1 i =
        ∑ j, -Real.log ((Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) ^ f (T.equivFin.symm j).1) * (γ.2 j : ℝ)) ∧
      (T.Nonempty → (fun j : Fin T.card =>
        -Real.log ((Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) ^ f (T.equivFin.symm j).1)) ≠ 0)  := by
  classical
  obtain ⟨Λ, Log, hLog, hmul, hmem, hdisc, hpf, -⟩ :=
    NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul K T
  set fz : Fin T.card → ℤ := fun j => (f (T.equivFin.symm j).1 : ℤ) with hfz
  have hfz0 : ∀ j, fz j ≠ 0 := fun j => by
    have := hf _ (T.equivFin.symm j).2
    simp only [hfz]; exact_mod_cast this.ne'
  set φ := R1L9.scale (r := Fintype.card (InfinitePlace K)) fz with hφ
  refine ⟨Λ.comap φ, Log, hLog, hmul, fun γ => ?_, ?_, fun γ hγ => ?_, fun hT => ?_⟩
  ·
    rw [AddSubgroup.mem_comap, hmem, R1L9.scale_apply]
  ·
    haveI := hdisc
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : Λ.comap φ => (⟨φ γ, γ.2⟩ : Λ)) ?_ ?_
    · exact (R1L9.continuous_scale fz).comp continuous_subtype_val |>.subtype_mk _
    · intro a b h
      apply Subtype.ext
      exact R1L9.scale_injective fz hfz0 (congrArg Subtype.val h)
  ·
    have h := hpf (φ γ) hγ
    rw [R1L9.scale_apply] at h
    simp only at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hfz, Int.cast_mul, Int.cast_natCast, Real.log_pow]
    ring
  ·
    obtain ⟨v, hv⟩ := hT
    rw [Function.ne_iff]
    refine ⟨T.equivFin ⟨v, hv⟩, ?_⟩
    simp only [Pi.zero_apply, Equiv.symm_apply_apply, neg_ne_zero]
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)) _
    · have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
        have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
          have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
          have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top
          omega
        exact_mod_cast h2
      exact (one_lt_pow₀ h1 (hf v hv).ne').ne'

end S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul
end P2MW
export P2MW.S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_div_sum_eq_neg_sum_log_pow_mul (solution)
