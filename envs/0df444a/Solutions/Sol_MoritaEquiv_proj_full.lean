-- Prove2me | solution 1 for MoritaEquiv.proj_full
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T20:44:01.372664+00:00
-- url     : https://prove2.me/submissions/d33b32c2-30f2-4893-9068-d4bc41952251

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_MoritaData_exists_extension_of_hom
import Theorems.Thm_MoritaEquiv_MoritaData_elemEmb_of_reduct

open CategoryTheory

namespace MoritaEquiv

namespace PFU

theorem emb_ext {L : Sig} {M N : Str L} {f g : ElemEmb M N} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

theorem pfu_full {L : Sig} {T : Theory L} (D : MoritaData L T) : D.proj.Full := by
  constructor
  intro N N' f
  obtain ⟨g, hg, hfun⟩ := MoritaData.exists_extension_of_hom D f
  have hold : ∀ {n : ℕ} {Γ : Fin n → L.Srt} (φ : Formula L Γ)
      (v : (i : Fin n) → (N.str.reduct D.incl).carrier (Γ i)),
      φ.Realize (N'.str.reduct D.incl) (fun i => g (D.incl.onSrt (Γ i)) (v i)) ↔
        φ.Realize (N.str.reduct D.incl) v := by
    intro n Γ φ v
    have e : (fun i => g (D.incl.onSrt (Γ i)) (v i)) = fun i => ElemEmb.toFun f (Γ i) (v i) :=
      funext fun i => hg _ _
    rw [e]
    exact ElemEmb.map_formula f φ v
  exact ⟨⟨g, MoritaData.elemEmb_of_reduct D N N' g hfun hold⟩, emb_ext (funext fun s => funext fun x => hg s x)⟩

end PFU
end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T) : D.proj.Full :=
  PFU.pfu_full D
