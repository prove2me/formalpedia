-- Prove2me | solution 1 for GlobalTheory.LaurentFlagBasis.exists_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:47.269936+00:00
-- url     : https://prove2.me/submissions/786baedb-4a00-4960-bb24-e26240a8eb8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
import Theorems.Thm_GlobalTheory_LaurentFlagBasis_exists_primitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory GlobalTheory.LaurentFlagBasis
variable {F : Type} [Field F]
namespace GlobalTheory.LaurentFlagBasis
theorem _root_.solution {n : ℕ} : ∀ (d : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)),
    d ≤ Module.finrank (LaurentSeries F) U →
    ∃ y : Fin d → (Fin n → PowerSeries F), (∀ b, lift (y b) ∈ U) ∧
      LinearIndependent F (fun b => red (y b))
  | 0, U, _ => ⟨Fin.elim0, fun b => b.elim0, linearIndependent_empty_type⟩
  | d+1, U, hd => by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := U) (by
      intro h; rw [h, finrank_bot] at hd; omega)
    obtain ⟨i, y0, hy0, hy0i⟩ := exists_primitive u hu0
    let f : U →ₗ[LaurentSeries F] LaurentSeries F := (LinearMap.proj i).comp U.subtype
    let U' : Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := (LinearMap.ker f).map U.subtype
    have hU' : d ≤ Module.finrank (LaurentSeries F) U' := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      have h2 : Module.finrank (LaurentSeries F) (LinearMap.range f) ≤ 1 := by
        simpa using Submodule.finrank_le (LinearMap.range f)
      have h3 : Module.finrank (LaurentSeries F) U' =
          Module.finrank (LaurentSeries F) (LinearMap.ker f) :=
        (Submodule.equivMapOfInjective _ U.injective_subtype _).finrank_eq.symm
      omega
    obtain ⟨y, hyU, hyi⟩ := solution d U' hU'
    refine ⟨Fin.cons y0 y, ?_, ?_⟩
    · intro b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp only [Fin.cons_zero]; rw [hy0]; exact U.smul_mem _ huU
      · simp only [Fin.cons_succ]
        obtain ⟨z, -, hz⟩ := Submodule.mem_map.mp (hyU b)
        rw [← hz]; exact z.2
    · have e : (fun b => red ((Fin.cons y0 y : Fin (d+1) → Fin n → PowerSeries F) b)) =
          Fin.cons (red y0) (fun b => red (y b)) := by
        ext b; refine Fin.cases ?_ (fun b => ?_) b <;> simp
      rw [e, linearIndependent_finCons]
      refine ⟨hyi, fun hmem => ?_⟩
      have hsub : Submodule.span F (Set.range fun b => red (y b)) ≤
          LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) i) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨z, hz, hzz⟩ := Submodule.mem_map.mp (hyU b)
        have hz0 : (z : Fin n → LaurentSeries F) i = 0 := hz
        have h0 : ((y b i : PowerSeries F) : LaurentSeries F) = 0 := by
          have := congrFun hzz i
          simp only [Submodule.subtype_apply] at this
          rw [← hz0, this]; rfl
        have h00 : y b i = 0 := by
          apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
          rw [map_zero]; exact h0
        simp [red, h00]
      have := hsub hmem
      simp [red, hy0i] at this
end GlobalTheory.LaurentFlagBasis
