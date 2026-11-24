-- Prove2me | solution 1 for GlobalTheory.RowLev.Inhab.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:15:38.016809+00:00
-- url     : https://prove2.me/submissions/40c1ab51-65fa-4422-a18f-cd4b96bd2e45

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_Inhab_exists_reduction
import Theorems.Thm_GlobalTheory_RowLev_Inhab_ker_eq_extId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Inhab
namespace GlobalTheory.RowLev.Inhab
theorem _root_.solution (I : AutInst) (hI : ∀ y, y ∈ I.Lf ↔ ∀ i, y i ∈ IntAf I.F I.E) (p : ℕ) (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 I.E)) (hw : Ideal.absNorm w.asIdeal = p) :
    ∃ fr : PlFrame I I.n p w, ∀ (y : I.Lf) (i : Fin I.n), fr.c y i = fr.r ⟨y.1 i, (hI y.1).1 y.2 i⟩ := by
  classical
  obtain ⟨r, hr⟩ := exists_reduction (F := I.F) p hp w hw
  have hk := ker_eq_extId hp.ne_zero r hr
  let c : I.Lf →ₛₗ[r] (Fin I.n → ZMod p) :=
    { toFun := fun y i => r ⟨y.1 i, (hI y.1).1 y.2 i⟩
      map_add' := fun x y => funext fun i => by
        rw [Pi.add_apply, ← map_add]; rfl
      map_smul' := fun a x => funext fun i => by
        have e : (⟨(a • x).1 i, (hI _).1 (a • x).2 i⟩ : IntAf I.F I.E) =
          a * ⟨x.1 i, (hI x.1).1 x.2 i⟩ := rfl
        show r _ = r a * r _
        rw [e, _root_.map_mul] }
  refine ⟨⟨r, fun a _ => hr a, c, ?_, fun y => ?_⟩, fun _ _ => rfl⟩
  · intro t
    choose s hs using ZMod.ringHom_surjective r
    exact ⟨⟨fun i => (s (t i) : I.E ⊗[I.F] Af I.F), (hI _).2 fun i => (s (t i)).2⟩, funext fun i => hs (t i)⟩
  rw [← Submodule.mem_smul_top_iff, ← hk]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have he : ∀ k, (Pi.single k 1 : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ I.Lf := fun k => (hI _).2 fun i => by
      by_cases h : i = k
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have e : y = ∑ k, (⟨y.1 k, (hI y.1).1 y.2 k⟩ : IntAf I.F I.E) • (⟨_, he k⟩ : I.Lf) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · show _ = y.1 j * (Pi.single j 1 : Fin I.n → I.E ⊗[I.F] Af I.F) j
        rw [Pi.single_eq_same, mul_one]
      · intro b _ hb
        show y.1 b * (Pi.single b 1 : Fin I.n → I.E ⊗[I.F] Af I.F) j = 0
        rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
      · exact fun h => absurd (Finset.mem_univ j) h
    rw [e]
    exact sum_mem fun k _ => Submodule.smul_mem_smul (congrFun h k) Submodule.mem_top
  · refine Submodule.smul_induction_on h (fun a ha x _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smulₛₗ, RingHom.mem_ker.1 ha, zero_smul]
    · rw [map_add, hx, hy, add_zero]
end GlobalTheory.RowLev.Inhab
