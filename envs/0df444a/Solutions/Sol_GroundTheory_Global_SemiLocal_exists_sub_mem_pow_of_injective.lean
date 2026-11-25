-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.exists_sub_mem_pow_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:59.283995+00:00
-- url     : https://prove2.me/submissions/ca4d6049-d5c9-4e62-9780-beb09719bdc5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter
noncomputable section
open GroundTheory.Global.SemiLocal
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum (𝓞 L)) (hw : Function.Injective w) (i : ι) (n : ℕ) :
    ∃ a : 𝓞 L, ∀ j, a - (if j = i then 1 else 0) ∈ (w j).asIdeal ^ n := by
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun j ↦ (w j).asIdeal) (fun _ ↦ n) (fun j _ ↦ (w j).prime)
    (fun j _ k _ hjk h ↦ hjk (hw (HeightOneSpectrum.ext h)))
    (fun j ↦ if j.1 = i then 1 else 0)
  exact ⟨y, fun j ↦ hy j (Finset.mem_univ j)⟩
end GroundTheory.Global.SemiLocal
