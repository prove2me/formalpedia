-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.mem_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:28.867785+00:00
-- url     : https://prove2.me/submissions/ff3449eb-7159-4c11-9f2e-92942b848caa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_periodLatticeSesquilinearForm_isHerm
import Theorems.Thm_GlobalTheory_ThetaInter_altE_swap
import Theorems.Thm_GlobalTheory_abs_im_latticeForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution {x : ℂ} (h : ∀ y ∈ L.lattice, ∃ m : ℤ, altE (form1 L) x y = m) : x ∈ L.lattice := by
  obtain ⟨a, ha⟩ := h _ L.ω₁_mem_lattice
  obtain ⟨b, hb⟩ := h _ L.ω₂_mem_lattice
  have hx := L.basis.sum_repr x
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hx
  set s := L.basis.repr x 0
  set t := L.basis.repr x 1
  have hs : ∀ u : ℂ, altE (form1 L) u u = 0 := fun u => by
    have := altE_swap (periodLatticeSesquilinearForm_isHerm L) u u
    linarith
  have e : ∀ y, altE (form1 L) x y = s * altE (form1 L) L.ω₁ y + t * altE (form1 L) L.ω₂ y := by
    intro y
    rw [← altE_real_smul_left, ← altE_real_smul_left, ← hx]
    simp only [altE, map_add, LinearMap.add_apply, add_im]
  rw [e, hs] at ha hb
  rw [altE_swap (periodLatticeSesquilinearForm_isHerm L) L.ω₂] at hb
  have h1 : |altE (form1 L) L.ω₂ L.ω₁| = 1 := abs_im_latticeForm L
  rw [PeriodPair.mem_lattice]
  rcases (abs_eq zero_le_one).1 h1 with h2 | h2 <;> rw [h2] at ha hb
  · refine ⟨-b, a, ?_⟩
    rw [← hx, show s = -b by linarith, show t = a by linarith]
    simp
  · refine ⟨b, -a, ?_⟩
    rw [← hx, show s = b by linarith, show t = -a by linarith]
    simp
end GlobalTheory.Mem.Col2.ThetaVec
