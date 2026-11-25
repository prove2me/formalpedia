-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.opcyclesShortComplex_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:24.826602+00:00
-- url     : https://prove2.me/submissions/147273d9-1cf3-4dc1-a010-b39a60961047

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution (i : ℕ) (h : IsZero (C.homology i)) :
    (opcyclesShortComplex C i).ShortExact := by
  have hm : Mono (C.fromOpcycles i (i + 1)) := by
    have hex := ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (C.homologyι i) (C.fromOpcycles i (i + 1)) (by simp))
      (C.homologyIsKernel i (i + 1) (by simp))
    exact hex.mono_g (h.eq_zero_of_src _)
  have hex : (opcyclesShortComplex C i).Exact := by
    have h1 := ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp))
      (C.opcyclesIsCokernel i (i + 1) (by simp))
    let φ : ShortComplex.mk (C.d i (i + 1)) (C.pOpcycles (i + 1)) (by simp) ⟶
        opcyclesShortComplex C i :=
      { τ₁ := C.pOpcycles i, τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by simp [opcyclesShortComplex]
        comm₂₃ := by simp [opcyclesShortComplex] }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (C.pOpcycles i))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (C.X (i + 1))))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (C.opcycles (i + 1))))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h1
  exact
    { exact := hex
      mono_f := hm
      epi_g := inferInstanceAs (Epi (C.pOpcycles (i + 1))) }
end GlobalTheory.FiniteLengthComplex
