-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermFrame.adapted_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:13.371799+00:00
-- url     : https://prove2.me/submissions/eddc7395-66a6-4a52-ab6f-6c00e1b643b6

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermFrame
theorem _root_.solution {U : Submodule L V} {e f : V} {l : ℕ} {e' f' : Fin l → U} {W' : Submodule L U}
    {u0 : L} {u' : Fin l → L} {Λ : AddSubgroup V}
    (hsp : ∀ (a b : L), ∀ w ∈ U, (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖u0‖ ∧ ‖b‖ ≤ ‖u0‖⁻¹ ∧ w ∈ Λ))
    (had : IsAdapted (fun x y : U => h x y) e' f' W' u' (Λ.comap U.subtype.toAddMonoidHom)) :
    IsAdapted h (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype)
      (Fin.cons u0 u' : Fin (l + 1) → L) Λ := by
  intro a b w hw
  obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
  have hc := had (fun i => a i.succ) (fun i => b i.succ) w' hw'
  obtain ⟨w0, hw0⟩ : ∃ w0 : U, w0 = ∑ i, a i.succ • e' i + ∑ i, b i.succ • f' i + w' := ⟨_, rfl⟩
  rw [← hw0] at hc
  have hval : (w0 : V) = ∑ i, a i.succ • (e' i : V) + ∑ i, b i.succ • (f' i : V) + (w' : V) := by
    rw [hw0]
    simp
  have hrw : ∑ i, a i • (Fin.cons e (fun i => (e' i : V)) : Fin (l + 1) → V) i +
      ∑ i, b i • (Fin.cons f (fun i => (f' i : V)) : Fin (l + 1) → V) i + U.subtype w' =
      a 0 • e + b 0 • f + (w0 : V) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hval]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    abel
  have hc' : (w0 : V) ∈ Λ ↔ (∀ i, ‖a i.succ‖ ≤ ‖u' i‖) ∧ (∀ i, ‖b i.succ‖ ≤ ‖u' i‖⁻¹) ∧
      ‖h w' w'‖ ≤ 1 := hc
  rw [hrw, hsp _ _ _ w0.2, hc']
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
  tauto
end GlobalTheory.CompanionTheory.HermFrame
