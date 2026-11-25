-- Prove2me | solution 1 for GlobalTheory.TraceCount.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:04.415551+00:00
-- url     : https://prove2.me/submissions/41d8b71c-31c2-4d8d-8d95-765e6d3a0cb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesIndexFixedTraceLe
import Theorems.Thm_GlobalTheory_TraceCount_exists_gen_mod
import Theorems.Thm_GlobalTheory_TraceCount_fibre_count
import Theorems.Thm_GlobalTheory_TraceCount_relIndex_eq_mul
import Theorems.Thm_GlobalTheory_TraceCount_encard_le_mul
import Theorems.Thm_GlobalTheory_TraceCount_proj_rank
import Theorems.Thm_GlobalTheory_TraceCount_sub_count
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_Formalism_SLP_P_CountO_exists_gen_mod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.TraceCount
namespace GlobalTheory.TraceCount
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L₀ M : Submodule (𝓞 K) V) (U : Submodule K V) (x : ℕ), Submodule.IsLattice K L₀ → 1 ≤ x → ((({La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((x : ℝ) ^ (2 * (((Module.finrank K V) - Module.finrank K U : ℕ) : ℝ) + cf K)) := by
  intro K V _ _ _ _ _ _ _ _ L₀ M U x hL hx
  set S := {La : Submodule (𝓞 K) V | La ≤ L₀ ∧ idx L₀ La = x ∧ La ⊓ rs (𝓞 K) U = M} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨L₁, hL₁⟩
  · simp [h0]
  let f : V →ₗ[𝓞 K] (V ⧸ U) := U.mkQ.restrictScalars (𝓞 K)
  have hker : LinearMap.ker f = rs (𝓞 K) U := by
    ext v
    simp [f]
  have hker' : f.toAddMonoidHom.ker = (LinearMap.ker f).toAddSubgroup := rfl
  set m := M.toAddSubgroup.relIndex (L₀ ⊓ LinearMap.ker f).toAddSubgroup with hm
  have hidx : ∀ La ∈ S, x = m * (La.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup := by
    intro La hLa
    have h1 := relIndex_eq_mul f.toAddMonoidHom La.toAddSubgroup L₀.toAddSubgroup hLa.1
    have h2 : La.toAddSubgroup.relIndex L₀.toAddSubgroup = x := hLa.2.1
    have h3 : La ⊓ LinearMap.ker f = M := hker ▸ hLa.2.2
    rw [← h2, h1, hm, ← h3]
    rfl
  set j := (L₁.map f).toAddSubgroup.relIndex (L₀.map f).toAddSubgroup with hj
  have hxj : x = m * j := hidx L₁ hL₁
  have hm0 : m ≠ 0 := fun h => by rw [h] at hxj; omega
  have hj0 : j ≠ 0 := fun h => by rw [h] at hxj; omega
  have hC : (L₀.map f).FG := (Submodule.IsLattice.fg (self := hL)).map f
  have hs : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  set s := Module.finrank K V - Module.finrank K U with hsdef
  obtain ⟨hT, hTc⟩ := sub_count (L₀.map f) hC j (Nat.one_le_iff_ne_zero.2 hj0)
  rw [hs] at hTc
  have hfinq : Finite (𝓞 K ⧸ Ideal.span {(m : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hm0)
  have hcount := encard_le_mul (fun La : Submodule (𝓞 K) V => La.map f) S _ hT (m ^ s)
    (fun La hLa => ⟨Submodule.map_mono hLa.1,
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) ((hidx La hLa).symm.trans hxj)⟩)
    (fun N hN => by
      have hCf : Module.Finite (𝓞 K) (L₀.map f) := Module.Finite.iff_fg.2 hC
      have hNfg : N.FG := Submodule.FG.of_le_of_isNoetherian hN.1
      obtain ⟨h1, h2, h3⟩ := proj_rank N hNfg
      obtain ⟨c, hc, hgen⟩ := exists_gen_mod N m
      have h4 := fibre_count f L₀ M N m _ hm.symm hm0 c hc hgen
      refine le_trans (Set.encard_le_encard ?_) (h4.trans ?_)
      · rintro La ⟨hLa, hN'⟩
        exact ⟨hLa.1, hN', hker ▸ hLa.2.2⟩
      · exact_mod_cast Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm0) (hs ▸ h3))
  refine le_trans (ENat.toENNReal_le.2 hcount) ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hjx : (j : ℝ) ≤ x := by exact_mod_cast hxj ▸ Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hm0)
  have hlog : 0 ≤ Real.logb 2 (Module.finrank ℚ K) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K))
  have hxr : (x : ℝ) = m * j := by exact_mod_cast hxj
  push_cast
  calc _ ≤ ((j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (j : ℝ) ^ s) * (m : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hTc (by positivity)
    _ = (j : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s := by rw [hxr, mul_pow]; ring
    _ ≤ (x : ℝ) ^ Real.logb 2 (Module.finrank ℚ K) * (x : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hjx hlog) (by positivity)
    _ = (x : ℝ) ^ (Real.logb 2 (Module.finrank ℚ K) + (s : ℝ)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
        unfold cf
        linarith)
end GlobalTheory.TraceCount
