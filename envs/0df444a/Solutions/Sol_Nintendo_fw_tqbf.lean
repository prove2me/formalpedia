-- Prove2me | solution 1 for Nintendo.fw_tqbf
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:59:02.312909+00:00
-- url     : https://prove2.me/submissions/dc98453d-e3be-40bc-9398-5f4c6265532f

import Mathlib
import Definitions.Def_Nintendo_sat
import Definitions.Def_Nintendo_game
import Definitions.Def_Nintendo_worlds

open Nintendo

theorem solution : ¬ HardTqbf qfGame qfStart qfGoal qfLevelSize := by
  rintro ⟨C, h⟩
  let ψ : QForm := ([Quant.ex, Quant.univ], [[Lit.pos 0]])
  have hψ : IsQbf ψ := by
    intro c hc
    simp [ψ] at hc
    subst hc
    simp
  have hiff := (h ψ hψ).2
  have hF : ¬ QTrue ψ := by
    simp [QTrue, ψ, qtrue, evalForm, evalClause, evalLit]
  apply hF
  rw [hiff]
  refine ⟨QFConf.finish, rfl, ?_⟩
  have st : ∀ u v, qfStep ψ u v → (qfGame ψ).step u v := fun _ _ h => h
  have r1 : Reachable (qfGame ψ) (qfStart ψ) (QFConf.row []) :=
    .step (.refl _) (st _ _ rfl)
  have r2 := r1.step (v := QFConf.row [true]) (st _ _ ⟨true, rfl, by decide, fun _ => rfl⟩)
  have r3 := r2.step (v := QFConf.row [true, true]) (st _ _ ⟨true, rfl, by decide, fun _ => rfl⟩)
  have r4 := r3.step (v := QFConf.test [true, true] 0) (st _ _ ⟨rfl, rfl, rfl⟩)
  have r5 := r4.step (v := QFConf.test [true, true] 1) (st _ _ ⟨rfl, rfl, by decide, by decide⟩)
  have r6 := r5.step (v := QFConf.back [true, true] 1) (st _ _ ⟨rfl, le_refl _, by decide⟩)
  have r7 := r6.step (v := QFConf.row [true, false]) (st _ _ ⟨by decide, by decide⟩)
  have r8 := r7.step (v := QFConf.test [true, false] 0) (st _ _ ⟨rfl, rfl, rfl⟩)
  have r9 := r8.step (v := QFConf.test [true, false] 1) (st _ _ ⟨rfl, rfl, by decide, by decide⟩)
  have r10 := r9.step (v := QFConf.back [true, false] 1) (st _ _ ⟨rfl, le_refl _, by decide⟩)
  exact r10.step (st _ _ ⟨by decide, by decide⟩)

