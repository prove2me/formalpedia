-- Prove2me | solution 1 for GlobalTheory.SW.exists_linearIndependent_prod_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:11.942785+00:00
-- url     : https://prove2.me/submissions/7e028757-5e51-4d11-9cdb-6d09077e31b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_SW_exists_linearIndependent_of_rat_independent
import Theorems.Thm_GlobalTheory_SW_prod_pow_le_prod_of_mono
import Theorems.Thm_GlobalTheory_discreteTopology_span_of_linearIndependent
import Theorems.Thm_GlobalTheory_exists_linearIndependent_norm_le_succMin
import Theorems.Thm_GlobalTheory_finrank_span_eq_finrank_int
import Theorems.Thm_GlobalTheory_prod_succMin_le_rpow_mul_spanCovol
import Theorems.Thm_GlobalTheory_spanCovol_span
import Theorems.Thm_GlobalTheory_succMin_mono
import Theorems.Thm_GlobalTheory_succMin_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution {E U V ι : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι] {N : ℕ}
    (hι : Fintype.card ι = Module.finrank ℚ E * N) (φ : U →ₗ[ℤ] V) (u : ι → U)
    (hu : LinearIndependent ℝ fun k => φ (u k)) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ (∀ i, w i ∈ Submodule.span ℤ (Set.range u)) ∧
      ∏ i, ‖φ (w i)‖ ^ Module.finrank ℚ E ≤
        (Fintype.card ι : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * √(gram ℝ fun k => φ (u k)).det := by
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  set L := Submodule.span ℤ (Set.range fun k => φ (u k)) with hL
  have : DiscreteTopology L := discreteTopology_span_of_linearIndependent hu
  have huZ : LinearIndependent ℤ fun k => φ (u k) := hu.restrict_scalars' ℤ
  have hr : Module.finrank ℤ L = Fintype.card ι := finrank_span_eq_card huZ
  have hrR : Module.finrank ℝ (Submodule.span ℝ (L : Set V)) = d * N := by
    rw [finrank_span_eq_finrank_int, hr, hι]
  have hLm : L = (Submodule.span ℤ (Set.range u)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  obtain ⟨w, hw, hS⟩ := exists_linearIndependent_of_rat_independent (E := E)
    (fun i => {t | t ∈ Submodule.span ℤ (Set.range u) ∧ ‖φ t‖ ≤ succMin L (d * i + 1)}) N (by
      intro i hi
      obtain ⟨v, hv, hvL⟩ := exists_linearIndependent_norm_le_succMin (L := L) (i := d * i + 1)
        (by rw [hrR]; nlinarith)
      have : ∀ k, ∃ t ∈ Submodule.span ℤ (Set.range u), φ t = v k := fun k => by
        have := (hvL k).1
        rwa [hLm] at this
      choose t ht htv using this
      refine ⟨t, (LinearIndependent.iff_fractionRing ℤ ℚ).1 (LinearIndependent.of_comp φ ?_),
        fun k => ⟨ht k, ?_⟩⟩
      · have : φ ∘ t = v := funext htv
        rw [this]; exact hv.restrict_scalars' ℤ
      · rw [htv]; exact (hvL k).2)
  refine ⟨w, hw, fun i => (hS i).1, ?_⟩
  have h1 := prod_succMin_le_rpow_mul_spanCovol L
  rw [spanCovol_span huZ, Fin.prod_univ_eq_prod_range (fun i => succMin L (i + 1)), hr] at h1
  refine le_trans ?_ h1
  rw [hι]
  refine le_trans ?_ (prod_pow_le_prod_of_mono (succMin L) (succMin_nonneg L) d N
    fun i j hij hj => succMin_mono hij (by rwa [hrR]))
  rw [← Fin.prod_univ_eq_prod_range (fun i => succMin L (d * i + 1) ^ d)]
  exact Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hS i).2 _
end GlobalTheory.SW
