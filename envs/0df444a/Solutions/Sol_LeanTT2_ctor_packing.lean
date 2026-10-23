-- Prove2me | solution 1 for LeanTT2.ctor_packing
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:31:39.561776+00:00
-- url     : https://prove2.me/submissions/0c5a00ff-32ae-4e6e-a3c1-02340c517f15

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

open LeanTT2

/-- three codes: the universe, the type `A → Univ`, and everything else -/
inductive G80tTm | U | PU | O
  deriving DecidableEq

/-- A degenerate model of the fragment: nothing is typed at a type `A → Univ`, and terms may be
typed at the universe only in the base context `true`. -/
def g80tF : Frag.{0} where
  E := ULift.{0} G80tTm
  Ctx := ULift.{0} Bool
  ok := fun _ => True
  isType := fun _ T => T.down = .O
  isProp := fun _ T => T.down = .O
  ty := fun Γ _ T => T.down ≠ .PU ∧ (T.down = .U → Γ.down = true)
  deq := fun _ _ _ => True
  red := fun _ _ _ => True
  alg := fun _ _ _ => True
  aty := fun _ _ _ => True
  ext := fun _ _ => ⟨false⟩
  var0 := ⟨.O⟩
  wkT := fun _ => ⟨.O⟩
  substT := fun _ _ => ⟨.O⟩
  app := fun _ _ => ⟨.O⟩
  lamT := fun _ _ => ⟨.O⟩
  piT := fun _ β => if β.down = .U then ⟨.PU⟩ else ⟨.O⟩
  Univ := ⟨.U⟩
  oneT := ⟨.O⟩
  unitT := ⟨.O⟩
  idf := fun _ => ⟨.O⟩
  sigmaT := fun _ _ => ⟨.O⟩
  pairT := fun _ _ => ⟨.O⟩
  fst := fun _ => ⟨.O⟩
  snd := fun _ => ⟨.O⟩
  sumT := fun _ _ => ⟨.O⟩
  inl := fun _ => ⟨.O⟩
  inr := fun _ => ⟨.O⟩
  caseT := fun _ _ _ => ⟨.O⟩
  up := fun _ => ⟨.O⟩
  down := fun _ => ⟨.O⟩
  truncT := fun _ => ⟨.O⟩
  wT := fun _ _ => ⟨.O⟩
  supT := fun _ _ => ⟨.O⟩
  recW := fun _ _ => ⟨.O⟩
  recW_cont := fun _ _ => ⟨.O⟩
  eqT := fun _ _ _ => ⟨.O⟩
  reflT := fun _ => ⟨.O⟩
  recEq := fun _ _ _ => ⟨.O⟩
  accT := fun _ _ => ⟨.O⟩
  introAcc := fun _ _ => ⟨.O⟩
  recAcc := fun _ _ _ => ⟨.O⟩
  recAcc_cont := fun _ _ => ⟨.O⟩
  deq_refl := fun _ _ => trivial
  deq_symm := fun _ _ _ _ => trivial
  deq_trans := fun _ _ _ _ _ _ => trivial
  deq_app := fun _ _ _ _ _ _ _ => trivial
  red_deq := fun _ _ _ _ => trivial
  ty_var0 := fun _ α hα => by
    refine ⟨?_, ?_⟩ <;> intro h <;> rw [hα] at h <;> cases h
  ty_wk := fun _ _ _ _ _ => ⟨by decide, by intro h; cases h⟩
  ty_pi := fun _ α β _ hβ => by
    show (if β.down = .U then (⟨.PU⟩ : ULift.{0} G80tTm) else ⟨.O⟩).down = .O
    rw [hβ]; rfl
  ty_lam := fun _ α b β _ hb => by
    obtain ⟨h1, h2⟩ := hb
    have hU : β.down ≠ .U := fun h => by simpa using h2 h
    show (if β.down = .U then (⟨.PU⟩ : ULift.{0} G80tTm) else ⟨.O⟩).down ≠ .PU ∧ _
    rw [if_neg hU]
    exact ⟨by decide, by intro h; cases h⟩
  ty_app := fun _ _ _ _ _ _ _ => ⟨by decide, by intro h; cases h⟩
  ty_beta := fun _ _ _ _ => trivial
  isType_one := fun _ => rfl
  ty_unit := fun _ => ⟨by decide, by intro h; cases h⟩
  isType_of_isProp := fun _ _ h => h
  ty_sigma := fun _ _ _ _ _ => rfl
  ty_sum := fun _ _ _ _ _ => rfl
  ty_w := fun _ _ _ _ _ => rfl
  ty_trunc := fun _ _ _ => rfl
  deq_irrel := fun _ _ _ _ _ _ _ => trivial
  alg_irrel := fun _ _ _ _ _ _ _ => trivial
  alg_symm := fun _ _ _ _ => trivial
  aty_conv := fun _ _ _ _ _ _ => trivial
  aty_idf := fun _ _ _ _ _ => Iff.rfl
  red_idf := fun _ _ _ => trivial
  red_fst := fun _ _ _ => trivial
  red_snd := fun _ _ _ => trivial
  red_case_inl := fun _ _ _ _ => trivial
  red_case_inr := fun _ _ _ _ => trivial
  red_down_up := fun _ _ => trivial
  red_recW := fun _ _ _ _ => trivial
  red_recEq := fun _ _ _ => trivial
  red_recAcc := fun _ _ _ _ => trivial

/-- the empty inductive specification in the base context -/
def g80tSp : IndSpec g80tF where
  Γ := ⟨true⟩
  hΓ := trivial
  n := 0
  SN := Fin.elim0
  SR := Fin.elim0
  CTy := Fin.elim0
  RecTy := ⟨.O⟩
  step := Fin.elim0
  small := false
  hSN := fun i => i.elim0
  hSR := fun i => i.elim0
  hCTy := fun i => i.elim0
  hRecTy := ⟨by decide, fun _ => rfl⟩
  hstep := fun i => i.elim0

theorem solution : ¬ (∀ (F : Frag.{0}) (Sp : IndSpec F),
    ∃ A B, F.isType Sp.Γ A ∧ F.ty Sp.Γ B (F.piT A F.Univ) ∧
      ∀ i : Fin Sp.n, ∃ c, F.ty Sp.Γ c (F.piT (Sp.SN i) A) ∧
        ∀ a, F.deq Sp.Γ (F.app B (F.app c a)) (F.app (Sp.SR i) a)) := by
  intro H
  obtain ⟨A, B, -, hB, -⟩ := H g80tF g80tSp
  exact hB.1 rfl
