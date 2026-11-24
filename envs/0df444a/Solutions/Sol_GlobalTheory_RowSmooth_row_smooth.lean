-- Prove2me | solution 1 for GlobalTheory.RowSmooth.row_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:36.776434+00:00
-- url     : https://prove2.me/submissions/89335d5f-b212-4423-ae11-e8ff8c74a652

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TestFunctionLocallyInvariant
import Theorems.Thm_GlobalTheory_TestFn_unif_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.RowSmooth
namespace GlobalTheory.RowSmooth
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (T : R × R → ℂ), IsTest T → ∃ U ∈ 𝓝 (0 : R), ∀ k : SpecialLinearGroup (Fin 2) R, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ U) → ∀ c u : R, T (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) = T (c, u) := by
  intro R _ _ _ T hT
  classical
  obtain ⟨V, hV, hVT⟩ := GlobalTheory.TestFn.unif_const (R × R) T hT
  have hC : IsCompact (tsupport T) := hT.2
  let φ : (R × R × R × R) → R × R → R × R := fun e v =>
    (v.1 * e.1 + v.2 * e.2.2.1, v.1 * e.2.1 + v.2 * e.2.2.2)
  have hφ : Continuous (fun z : (R × R × R × R) × (R × R) => φ z.1 z.2) := by
    simp only [φ]; fun_prop
  have hev : ∀ᶠ e in 𝓝 (0 : R × R × R × R), ∀ v ∈ tsupport T, φ e v ∈ V := by
    refine hC.eventually_forall_of_forall_eventually (P := fun e v => φ e v ∈ V) ?_
    intro v _
    have h0 : φ 0 v = 0 := by simp [φ]
    have : V ∈ 𝓝 (φ (0 : R × R × R × R) v) := by rw [h0]; exact hV
    exact hφ.continuousAt (x := ((0 : R × R × R × R), v)) this
  obtain ⟨A₁, hA₁, S₁, hS₁, hsub₁⟩ := mem_nhds_prod_iff.mp (show _ ∈ 𝓝 ((0 : R), ((0 : R), (0 : R), (0 : R))) from hev)
  obtain ⟨A₂, hA₂, S₂, hS₂, hsub₂⟩ := mem_nhds_prod_iff.mp hS₁
  obtain ⟨A₃, hA₃, A₄, hA₄, hsub₃⟩ := mem_nhds_prod_iff.mp hS₂
  set U₀ : Set R := A₁ ∩ A₂ ∩ A₃ ∩ A₄ with hU₀def
  have hU₀ : U₀ ∈ 𝓝 (0 : R) := inter_mem (inter_mem (inter_mem hA₁ hA₂) hA₃) hA₄
  have key : ∀ a b c d : R, a ∈ U₀ → b ∈ U₀ → c ∈ U₀ → d ∈ U₀ → ∀ v ∈ tsupport T,
      T (v + φ (a, b, c, d) v) = T v := by
    intro a b c d ha hb hc hd v hv
    have hmem : ((a, b, c, d) : R × R × R × R) ∈ {e | ∀ v ∈ tsupport T, φ e v ∈ V} :=
      hsub₁ ⟨ha.1.1.1, hsub₂ ⟨hb.1.1.2, hsub₃ ⟨hc.1.2, hd.2⟩⟩⟩
    exact hVT v _ (hmem v hv)
  refine ⟨U₀ ∩ (fun x => -x) ⁻¹' U₀, inter_mem hU₀
    (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU₀)), ?_⟩
  intro k hk c u
  have hdet : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by
    have := k.2; rw [Matrix.det_fin_two] at this; exact this
  have e00 := hk 0 0
  have e01 := hk 0 1
  have e10 := hk 1 0
  have e11 := hk 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at e00 e01 e10 e11
  by_cases hv : (c, u) ∈ tsupport T
  · have := key (k 0 0 - 1) (k 0 1) (k 1 0) (k 1 1 - 1) e00.1 e01.1 e10.1 e11.1 (c, u) hv
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext <;> simp <;> ring
  by_cases hw : (c * k 0 0 + u * k 1 0, c * k 0 1 + u * k 1 1) ∈ tsupport T
  · have := key (k 1 1 - 1) (-k 0 1) (-k 1 0) (k 0 0 - 1) e11.1 e01.2 e10.2 e00.1 _ hw
    rw [← this]
    congr 1
    simp only [φ, Prod.mk_add_mk]
    ext
    · simp; linear_combination c * hdet
    · simp; linear_combination u * hdet
  · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]
end GlobalTheory.RowSmooth
