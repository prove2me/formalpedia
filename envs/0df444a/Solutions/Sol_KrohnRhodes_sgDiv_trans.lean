-- Prove2me | solution 1 for KrohnRhodes.sgDiv_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:36.057362+00:00
-- url     : https://prove2.me/submissions/eea41663-03d6-46e6-85d0-bb365652f262

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
open KrohnRhodes
universe u
variable {M : Type u} [Monoid M] [Finite M] [DecidableEq M]
namespace KrohnRhodes
theorem _root_.solution {S T U : Type u} [Mul S] [Mul T] [Mul U]
    (hST : SgDiv S T) (hTU : SgDiv T U) : SgDiv S U := by
  obtain ⟨V, φ, hφ⟩ := hST
  obtain ⟨W, ψ, hψ⟩ := hTU
  -- Pull `V ⊆ T` back along `ψ : W → T` to a subsemigroup of `U`.
  let W' : Subsemigroup U :=
    { carrier := {u | ∃ h : u ∈ W, ψ ⟨u, h⟩ ∈ V}
      mul_mem' := by
        rintro a b ⟨ha, hav⟩ ⟨hb, hbv⟩
        refine ⟨W.mul_mem ha hb, ?_⟩
        have : ψ ⟨a * b, W.mul_mem ha hb⟩ = ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ :=
          ψ.map_mul ⟨a, ha⟩ ⟨b, hb⟩
        rw [this]
        exact V.mul_mem hav hbv }
  refine ⟨W', ⟨fun u => φ ⟨ψ ⟨u.1, u.2.1⟩, u.2.2⟩, ?_⟩, ?_⟩
  · -- multiplicativity
    rintro ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
    have hψm : ψ ⟨a * b, W.mul_mem ha hb⟩ = ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ :=
      ψ.map_mul ⟨a, ha⟩ ⟨b, hb⟩
    show φ ⟨ψ ⟨a * b, W.mul_mem ha hb⟩, _⟩
      = φ ⟨ψ ⟨a, ha⟩, hav⟩ * φ ⟨ψ ⟨b, hb⟩, hbv⟩
    have : φ ⟨ψ ⟨a * b, W.mul_mem ha hb⟩, by rw [hψm]; exact V.mul_mem hav hbv⟩
        = φ (⟨ψ ⟨a, ha⟩, hav⟩ * ⟨ψ ⟨b, hb⟩, hbv⟩) := by
      congr 1
      apply Subtype.ext
      exact hψm
    rw [this, φ.map_mul]
  · -- surjectivity
    intro s
    obtain ⟨v, hv⟩ := hφ s
    obtain ⟨w, hw⟩ := hψ (v : T)
    have hw' : ψ ⟨(w : U), w.2⟩ = (v : T) := hw
    have hmem : ψ ⟨(w : U), w.2⟩ ∈ V := by rw [hw']; exact v.2
    refine ⟨⟨(w : U), w.2, hmem⟩, ?_⟩
    show φ ⟨ψ ⟨(w : U), w.2⟩, hmem⟩ = s
    have : φ ⟨ψ ⟨(w : U), w.2⟩, hmem⟩ = φ v := by
      congr 1
      exact Subtype.ext hw'
    rw [this, hv]
end KrohnRhodes
