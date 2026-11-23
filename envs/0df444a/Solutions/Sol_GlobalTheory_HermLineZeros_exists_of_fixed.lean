-- Prove2me | solution 1 for GlobalTheory.HermLineZeros.exists_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:13.588741+00:00
-- url     : https://prove2.me/submissions/22365c9d-9322-4f74-b28a-68fa0a5bc684

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Theorems.Thm_GlobalTheory_HermLineZeros_exists_conj_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HermLineZeros
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.HermLineZeros
namespace _root_.GlobalTheory.HermLineZeros
theorem _root_.solution (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.HermLineZeros.exists_conj_ne h
  let S : Subalgebra F E := AlgHom.equalizer σ (AlgHom.id F E)
  have hS : S ≠ ⊤ := by
    intro hS
    have hdS : d ∈ S := hS ▸ Algebra.mem_top
    exact hd hdS
  have hle : Module.finrank F S ≤ 2 :=
    h.2.2.1 ▸ Submodule.finrank_le (Subalgebra.toSubmodule S)
  have hne : Module.finrank F S ≠ 2 := by
    intro h2
    apply hS
    apply Subalgebra.toSubmodule.injective
    rw [Algebra.top_toSubmodule]
    exact Submodule.eq_top_of_finrank_eq (h2.trans h.2.2.1.symm)
  have hpos : 0 < Module.finrank F S := Module.finrank_pos
  have hbot : S = ⊥ := Subalgebra.finrank_eq_one_iff.mp (by omega)
  have heS : e ∈ S := he
  rw [hbot] at heS
  exact Algebra.mem_bot.mp heS
end _root_.GlobalTheory.HermLineZeros
end GlobalTheory.HermLineZeros
