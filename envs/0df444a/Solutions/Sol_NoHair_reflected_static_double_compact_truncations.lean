-- Prove2me | solution 1 for NoHair.reflected_static_double_compact_truncations
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:55:25.283166+00:00
-- url     : https://prove2.me/submissions/0598152e-bc23-44b6-b5ee-a574df960bd5

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (d : ReflectedStaticDouble Ω N h) :
    ∀ R : ℝ, IsCompact ((d.inc true '' {x : ↥(closure Ω) | R < ‖x.val‖}) ∪ (d.inc false '' {x : ↥(closure Ω) | R < ‖x.val‖}))ᶜ := by
  classical
  intro R
  let S := ↥(closure Ω)
  let K : Set S := {x | ‖x.val‖ ≤ R}
  let U : Set S := {x | R < ‖x.val‖}
  have Kcomp : IsCompact K := by
    have eq : K = Subtype.val ⁻¹' Metric.closedBall (0:ADMPoint) R := by
      ext x; simp [K,Metric.mem_closedBall,dist_zero_right]
    rw [eq]
    exact isClosed_closure.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall _ _)
  have same (a b : Bool) (x y : S) (e : d.inc a x = d.inc b y) : x=y := by
    cases a <;> cases b
    · exact (d.embedded false).injective e
    · exact ((d.seam _ _).mp e.symm).1.symm
    · exact ((d.seam _ _).mp e).1
    · exact (d.embedded true).injective e
  have excl (a b : Bool) (x : S) (hx : x∈K) : d.inc a x ∉ d.inc b '' U := by
    rintro ⟨y,hy,he⟩
    have xy := same b a y x he
    subst y
    change ‖x.val‖ ≤ R at hx
    change R < ‖x.val‖ at hy
    exact (not_lt_of_ge hx) hy
  have E : (d.inc true '' U ∪ d.inc false '' U)ᶜ = d.inc true '' K ∪ d.inc false '' K := by
    ext q
    constructor
    · intro hq
      obtain ⟨b,x,rfl⟩ := d.covers q
      have hx : x∈K := by
        by_contra hi
        change ¬ ‖x.val‖ ≤ R at hi
        have hx' : x∈U := (show R < ‖x.val‖ from lt_of_not_ge hi)
        cases b
        · exact hq (Or.inr ⟨x,hx',rfl⟩)
        · exact hq (Or.inl ⟨x,hx',rfl⟩)
      cases b
      · exact Or.inr ⟨x,hx,rfl⟩
      · exact Or.inl ⟨x,hx,rfl⟩
    · rintro (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩) (h|h)
      · exact excl true true x hx h
      · exact excl true false x hx h
      · exact excl false true x hx h
      · exact excl false false x hx h
  change IsCompact (d.inc true '' U ∪ d.inc false '' U)ᶜ
  rw [E]
  exact (Kcomp.image (d.inc true).continuous).union (Kcomp.image (d.inc false).continuous)
