-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_congruenceSubgroup_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:39:23.969321+00:00
-- url     : https://prove2.me/submissions/8c9ae1e9-84cf-4cd1-961d-4ea22126f53c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_one_apply_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {m : ℕ} {g : GL (Fin n) F}
    (h1 : ∀ i j, valuation F (g i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ m)
    (h2 : ∀ i j, valuation F ((g⁻¹ : GL (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
      valuation F ϖ ^ m) :
    g ∈ congruenceSubgroup F n m := by
  have hle : valuation F ϖ ^ m ≤ 1 := pow_le_one' (valuation_uniformizer_lt_one F).le m
  have hint : ∀ (x : F) (i j : Fin n),
      valuation F (x - (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ m → x ∈ 𝒪[F] := by
    intro x i j hx
    refine (Valuation.mem_integer_iff _ _).mpr ?_
    have : x = (x - (1 : Matrix (Fin n) (Fin n) F) i j) + (1 : Matrix (Fin n) (Fin n) F) i j := by
      ring
    rw [this]
    exact Valuation.map_add_le _ (hx.trans hle) (valuation_one_apply_le i j)
  rw [mem_congruenceSubgroup_iff F n, mem_integralGL_iff F n]
  exact ⟨⟨fun i j => hint _ i j (h1 i j), fun i j => hint _ i j (h2 i j)⟩, h1⟩
end GroundTheory.Automorphic.Parabolic
