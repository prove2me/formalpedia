-- Prove2me | solution 1 for LeanTT2.inductive_to_w
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:59.401217+00:00
-- url     : https://prove2.me/submissions/79a9ae33-db5b-456c-85f4-b04ac3add12f

import Mathlib
import Definitions.Def_LeanTT2_frag
import Definitions.Def_LeanTT2_spec
import Definitions.Def_LeanTT2_counter

universe u

open LeanTT2

theorem solution (F : Frag.{u}) (Sp : IndSpec F)
    (A B : F.E)
    (hA : F.isType Sp.Γ A)
    (hB : F.ty Sp.Γ B (F.piT A F.Univ))
    (hcover : ∀ i : Fin Sp.n, ∃ c, F.ty Sp.Γ c (F.piT (Sp.SN i) A) ∧
      ∀ a, F.deq Sp.Γ (F.app B (F.app c a)) (F.app (Sp.SR i) a))
    (hskel : F.isType Sp.Γ (F.wT A B))
    (hsub : Sp.small = true → F.isProp Sp.Γ (F.truncT (F.wT A B)))
    (hreal : ∃ (cs : Fin Sp.n → F.E) (r : F.E),
      (∀ i : Fin Sp.n, F.ty Sp.Γ (cs i) (Sp.CTy i)) ∧
      F.ty Sp.Γ r (F.piT (F.wT A B) Sp.RecTy) ∧
      (∀ (i : Fin Sp.n) (x : F.E),
        F.red Sp.Γ (F.app r (F.app (cs i) x)) (F.app (Sp.step i) x))) :
    ∃ R : Realizes F Sp, RealizesOK F Sp R := by
  obtain ⟨cs, r, hcs, hr, hiota⟩ := hreal
  exact ⟨⟨A, B, F.wT A B, cs, r⟩, hA, hB, hskel, F.deq_refl _ _, hcs, hcover, hr, hiota, hsub⟩
