-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a4_fourth_average_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:16:58.115754+00:00
-- url     : https://prove2.me/submissions/08507d50-477f-4dec-85d3-2c76d83d01f7

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P004
import Definitions.Def_OAIQ252P006
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_OperatorNorm_map_hybrid_fourth_average

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_DegreeCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/
namespace UniqueGamesTheorem.Appendix.DegreeCover

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Glue a linear map on P to zero on Q when the restrictions agree. -/
theorem exists_glue_zero (P Q : Submodule F2 W) (f : W →ₗ[F2] V)
    (cover : P ⊔ Q = ⊤) (compatible : ∀ w ∈ P, w ∈ Q → f w = 0) :
    ∃ g : W →ₗ[F2] V,
      (∀ w ∈ P, g w = f w) ∧ (∀ w ∈ Q, g w = 0) := by
  let p : W →ₗ.[F2] V := ⟨P, f.comp P.subtype⟩
  let q : W →ₗ.[F2] V := ⟨Q, 0⟩
  have hc : ∀ (x : p.domain) (y : q.domain), (x : W) = y → p x = q y := by
    intro x y hxy
    exact compatible x x.property (hxy ▸ y.property)
  let t := p.sup q hc
  have ht : ∀ w : W, w ∈ t.domain := by
    intro w
    change w ∈ P ⊔ Q
    rw [cover]
    exact Submodule.mem_top
  let inc : W →ₗ[F2] t.domain := (LinearMap.id : W →ₗ[F2] W).codRestrict t.domain ht
  refine ⟨t.toFun.comp inc, ?_, ?_⟩
  · intro w hw
    exact ((p.left_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm
  · intro w hw
    exact ((p.right_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm

end UniqueGamesTheorem.Appendix.DegreeCover

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

namespace UniqueGamesTheorem.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

variable [FiniteDimensional K W]

theorem rankBelow_iff (X Y : W →ₗ[K] V) :
    RankBelow X Y ↔
      Disjoint (LinearMap.range X) (LinearMap.range (Y - X)) ∧
        LinearMap.ker X ⊔ LinearMap.ker (Y - X) = ⊤ := by
  have h := finrank_add_eq_iff X (Y - X)
  rw [add_remainder] at h
  exact h

end UniqueGamesTheorem.Appendix.RankAdditivity

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_Identities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

theorem quotient_mem_image_iff (A₀ A : Submodule K V) (hA : A₀ ≤ A) (v : V) :
    A₀.mkQ v ∈ A.map A₀.mkQ ↔ v ∈ A := by
  change v ∈ (A.map A₀.mkQ).comap A₀.mkQ ↔ v ∈ A
  rw [Submodule.comap_map_mkQ, sup_of_le_right hA]

variable [FiniteDimensional K W]

/-! ## The unique selector in (A.4) -/

theorem a4_codomain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A₀ = (B.map Y) ⊓ A := by
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  apply le_antisymm
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hwX := hk hwy
    rw [hker] at hwX
    exact ⟨⟨w, hwX, hw⟩, hA ha⟩
  · intro a ha
    rcases ha.1 with ⟨b, hb, hYb⟩
    let bb : B₀ := ⟨b, hB hb⟩
    have hxb : X bb = 0 := by
      have hx : bb ∈ LinearMap.ker X := by rw [hker]; exact hb
      exact hx
    have hymem : compress Y A₀ B₀ bb ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y b, by rw [hYb]; exact ha.2, rfl⟩
    have hzmem : compress Y A₀ B₀ bb ∈ LinearMap.range (compress Y A₀ B₀ - X) :=
      ⟨bb, by change compress Y A₀ B₀ bb - X bb = compress Y A₀ B₀ bb; rw [hxb, sub_zero]⟩
    have hz := Submodule.disjoint_def.mp hd (compress Y A₀ B₀ bb) hymem hzmem
    have hm : Y b ∈ LinearMap.ker A₀.mkQ := hz
    rw [Submodule.ker_mkQ, hYb] at hm
    exact hm

theorem a4_domain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    B₀ = B ⊔ A.comap Y := by
  have hrange := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hcover := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).2
  apply le_antisymm
  · intro w hw
    let ww : B₀ := ⟨w, hw⟩
    have ht : ww ∈ LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) := by
      rw [hcover]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨b, hb, p, hp, hbp⟩
    have hbB : (b : W) ∈ B := by rw [hker] at hb; exact hb
    have hpEq : compress Y A₀ B₀ p = X p := by
      have hz : compress Y A₀ B₀ p - X p = 0 := hp
      exact sub_eq_zero.mp hz
    have hq : A₀.mkQ (Y p) ∈ A.map A₀.mkQ := by
      rw [← himage]
      change compress Y A₀ B₀ p ∈ LinearMap.range X
      rw [hpEq]
      exact ⟨p, rfl⟩
    have hpA : (p : W) ∈ A.comap Y :=
      (quotient_mem_image_iff A₀ A hA (Y p)).mp hq
    exact Submodule.mem_sup.mpr ⟨(b : W), hbB, (p : W), hpA, congrArg Subtype.val hbp⟩
  · apply sup_le hB
    intro w hw
    have hqx : A₀.mkQ (Y w) ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y w, hw, rfl⟩
    rcases hrange hqx with ⟨c, hc⟩
    have hdiff : Y w - Y c ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc.symm
    have hwc : w - c ∈ B₀ := inner.2 (by
      change Y (w - c) ∈ A₀
      simpa only [map_sub] using hdiff)
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

theorem a4_apply_on_preimage (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀))
    (p : B₀) (hp : Y p ∈ A) : X p = A₀.mkQ (Y p) := by
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  have hy : compress Y A₀ B₀ p ∈ LinearMap.range X := by
    rw [himage]
    exact ⟨Y p, hp, rfl⟩
  have hx : X p ∈ LinearMap.range X := ⟨p, rfl⟩
  have hzX : (compress Y A₀ B₀ - X) p ∈ LinearMap.range X :=
    (LinearMap.range X).sub_mem hy hx
  have hzR : (compress Y A₀ B₀ - X) p ∈ LinearMap.range (compress Y A₀ B₀ - X) := ⟨p, rfl⟩
  have hz := Submodule.disjoint_def.mp hd ((compress Y A₀ B₀ - X) p) hzX hzR
  exact (sub_eq_zero.mp hz).symm

theorem a4_map_unique (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X₁ X₂ : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hk₁ : LinearMap.ker X₁ = B.comap B₀.subtype)
    (hk₂ : LinearMap.ker X₂ = B.comap B₀.subtype)
    (hi₁ : LinearMap.range X₁ = A.map A₀.mkQ)
    (hi₂ : LinearMap.range X₂ = A.map A₀.mkQ)
    (hr₁ : RankAdditivity.RankBelow X₁ (compress Y A₀ B₀))
    (hr₂ : RankAdditivity.RankBelow X₂ (compress Y A₀ B₀)) : X₁ = X₂ := by
  have hd := a4_domain_forced Y A₀ A B B₀ X₁ hA hB inner hk₁ hi₁ hr₁
  ext w
  have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hd]; exact w.property
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
  let bb : B₀ := ⟨b, hB hb⟩
  have hpB₀ : p ∈ B₀ := by rw [hd]; exact Submodule.mem_sup_right hp
  let pp : B₀ := ⟨p, hpB₀⟩
  have heq : w = bb + pp := Subtype.ext hbp.symm
  have hb₁ : X₁ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₁ := by rw [hk₁]; exact hb
    exact h
  have hb₂ : X₂ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₂ := by rw [hk₂]; exact hb
    exact h
  have hp₁ := a4_apply_on_preimage Y A₀ A B₀ X₁ hi₁ hr₁ pp hp
  have hp₂ := a4_apply_on_preimage Y A₀ A B₀ X₂ hi₂ hr₂ pp hp
  rw [heq, map_add, map_add, hb₁, hb₂, hp₁, hp₂]

theorem a4_weak_selector_of_summand (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B := by
  have hi := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    have hqa : A₀.mkQ a ∈ LinearMap.range X := by rw [himage]; exact ⟨a, ha, rfl⟩
    rcases hi hqa with ⟨c, hc⟩
    have hdiff : Y c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc
    rcases inner.1 hdiff with ⟨w, hw⟩
    refine ⟨(c : W) - w, ?_⟩
    rw [map_sub, hw]
    abel
  · intro w hw
    have hyw : Y w = 0 := hw
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hyw]; exact A₀.zero_mem)
    have hwq : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change A₀.mkQ (Y w) = 0
      rw [hyw, map_zero]
    have hwx := hk hwq
    rw [hker] at hwx
    exact hwx

omit [FiniteDimensional K W] in
theorem a4_kernel_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA₀ : A₀ = (B.map Y) ⊓ A) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hKY : LinearMap.ker Y ≤ B)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.ker X = B.comap B₀.subtype := by
  ext w
  constructor
  · intro hw
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    have hxp : X pp = 0 := by
      have hxw : X w = 0 := hw
      rw [heq, map_add, hzero bb hb, zero_add] at hxw
      exact hxw
    have hqp : A₀.mkQ (Y p) = 0 := (hcopy pp hp).symm.trans hxp
    have hy₀ : Y p ∈ A₀ := by
      have hm : Y p ∈ LinearMap.ker A₀.mkQ := hqp
      simpa only [Submodule.ker_mkQ] using hm
    rw [hA₀] at hy₀
    rcases hy₀.1 with ⟨b', hb', hYb'⟩
    have hpk : p - b' ∈ LinearMap.ker Y := by
      change Y (p - b') = 0
      rw [map_sub, hYb', sub_self]
    have hpB : p ∈ B := by
      have h := B.add_mem (hKY hpk) hb'
      simpa only [sub_add_cancel] using h
    have h := B.add_mem hb hpB
    change (w : W) ∈ B
    exact hbp ▸ h
  · intro hw
    exact hzero w hw

theorem disjoint_quotient_images_of_intersection
    (A₀ A C : Submodule K V) (hA₀ : A₀ = C ⊓ A) :
    Disjoint (A.map A₀.mkQ) (C.map A₀.mkQ) := by
  apply Submodule.disjoint_def.mpr
  intro v hvA hvC
  rcases hvA with ⟨a, ha, hqa⟩
  rcases hvC with ⟨c, hc, hqc⟩
  have hdiff : c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp (hqc.trans hqa.symm)
  have hdiffA : c - a ∈ A := by rw [hA₀] at hdiff; exact hdiff.2
  have hcA : c ∈ A := by
    have h := A.add_mem hdiffA ha
    simpa only [sub_add_cancel] using h
  have hc₀ : c ∈ A₀ := by rw [hA₀]; exact ⟨hc, hcA⟩
  have hqzero : A₀.mkQ c = 0 := by
    change c ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hc₀
  exact hqc.symm.trans hqzero

omit [FiniteDimensional K W] in
theorem a4_range_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hB₀ : B₀ = B ⊔ A.comap Y) (hAY : A ≤ LinearMap.range Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range X = A.map A₀.mkQ := by
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    refine ⟨Y p, hp, ?_⟩
    rw [← hw, heq, map_add, hzero bb hb, hcopy pp hp, zero_add]
  · rintro v ⟨a, ha, hqa⟩
    rcases hAY ha with ⟨p, hp⟩
    have hpA : p ∈ A.comap Y := by change Y p ∈ A; rw [hp]; exact ha
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hpA
    let pp : B₀ := ⟨p, hp₀⟩
    refine ⟨pp, ?_⟩
    rw [hcopy pp hpA, hp, hqa]

omit [FiniteDimensional K W] in
theorem a4_remainder_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range (compress Y A₀ B₀ - X) ≤ (B.map Y).map A₀.mkQ ∧
      LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) = ⊤ := by
  have decomp : ∀ w : B₀, ∃ b p : B₀,
      (b : W) ∈ B ∧ Y p ∈ A ∧ b + p = w := by
    intro w
    have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    exact ⟨⟨b, hb₀⟩, ⟨p, hp₀⟩, hb, hp, Subtype.ext hbp⟩
  constructor
  · rintro v ⟨w, hw⟩
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hz : (compress Y A₀ B₀ - X) w = A₀.mkQ (Y b) := by
      rw [← hbp, map_add]
      change (compress Y A₀ B₀ b - X b) + (compress Y A₀ B₀ p - X p) = A₀.mkQ (Y b)
      rw [hzero b hb, hcopy p hp]
      simp only [compress_apply, sub_zero, sub_self, add_zero]
    exact ⟨Y b, ⟨(b : W), hb, rfl⟩, hz.symm.trans hw⟩
  · apply le_antisymm le_top
    intro w _
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hpker : p ∈ LinearMap.ker (compress Y A₀ B₀ - X) := by
      change compress Y A₀ B₀ p - X p = 0
      rw [hcopy p hp]
      exact sub_self _
    exact Submodule.mem_sup.mpr ⟨b, hzero b hb, p, hpker, hbp⟩

theorem a4_surviving_index_unique (Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (p q : A4Index (K := K) (W := W) (V := V))
    (hp : A4Survives Y A B p) (hq : A4Survives Y A B q) : p = q := by
  rcases p with ⟨A₀, B₀, X₀⟩
  rcases q with ⟨A₁, B₁, X₁⟩
  rcases hp with ⟨ha₀, hb₀, hi₀, hk₀, him₀, hr₀⟩
  rcases hq with ⟨ha₁, hb₁, hi₁, hk₁, him₁, hr₁⟩
  have heA : A₀ = A₁ := (a4_codomain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_codomain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  have heB : B₀ = B₁ := (a4_domain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_domain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  subst A₁
  subst B₁
  have heX := a4_map_unique Y A₀ A B B₀ X₀ X₁ ha₀ hb₀ hi₀ hk₀ hk₁ him₀ him₁ hr₀ hr₁
  cases heX
  rfl

end UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.BinaryA4

open LinearIdentities

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 W]

omit [FiniteDimensional F2 W] in
/-- Construct the actual linear map in the canonical (A.4) summand by
gluing zero on `B` with `Q_A₀ Y` on `Y⁻¹(A)`. -/
theorem canonical_glued_map (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    ∃ X : ↥(B ⊔ A.comap Y) →ₗ[F2] (V ⧸ ((B.map Y) ⊓ A)),
      (∀ b : ↥(B ⊔ A.comap Y), (b : W) ∈ B → X b = 0) ∧
      (∀ p : ↥(B ⊔ A.comap Y), Y p ∈ A → X p = ((B.map Y) ⊓ A).mkQ (Y p)) := by
  let P := A.comap Y
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ P
  let pp := P.comap B₀.subtype
  let bb := B.comap B₀.subtype
  let f := compress Y A₀ B₀
  have hc : pp ⊔ bb = ⊤ := by
    apply le_antisymm le_top
    intro w _
    rcases Submodule.mem_sup.mp w.property with ⟨b, hb, p, hp, hbp⟩
    let pv : B₀ := ⟨p, Submodule.mem_sup_right hp⟩
    let bv : B₀ := ⟨b, Submodule.mem_sup_left hb⟩
    refine Submodule.mem_sup.mpr ⟨pv, hp, bv, hb, ?_⟩
    apply Subtype.ext
    change p + b = (w : W)
    rw [add_comm]
    exact hbp
  have compat : ∀ w ∈ pp, w ∈ bb → f w = 0 := by
    intro w hp hb
    have hm : Y w ∈ A₀ := ⟨⟨(w : W), hb, rfl⟩, hp⟩
    change Y w ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hm
  obtain ⟨X, hcopy, hzero⟩ := DegreeCover.exists_glue_zero pp bb f hc compat
  refine ⟨X, ?_, ?_⟩
  · intro b hb
    exact hzero b hb
  · intro p hp
    exact hcopy p hp

theorem a4_selector_exists (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hAY : A ≤ LinearMap.range Y) (hKY : LinearMap.ker Y ≤ B) :
    ∃ p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  obtain ⟨X, hzero, hcopy⟩ := canonical_glued_map Y A B
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ A.comap Y
  have inner : Hybrid Y A₀ B₀ := by
    constructor
    · intro a ha
      rcases ha.1 with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    · intro w hw
      have hy : Y w ∈ (B.map Y) ⊓ A := hw
      exact Submodule.mem_sup_right hy.2
  have hk := a4_kernel_of_gluing Y A₀ A B B₀ X rfl rfl hKY hzero hcopy
  have hi := a4_range_of_gluing Y A₀ A B B₀ X rfl hAY hzero hcopy
  have hr := a4_remainder_of_gluing Y A₀ A B B₀ X rfl hzero hcopy
  have hd := disjoint_quotient_images_of_intersection A₀ A (B.map Y) rfl
  have hl : RankAdditivity.RankBelow X (compress Y A₀ B₀) := by
    apply (RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mpr
    refine ⟨?_, hr.2⟩
    rw [hi]
    exact hd.mono_right hr.1
  exact ⟨⟨A₀, B₀, X⟩, inf_le_right, le_sup_left, inner, hk, hi, hl⟩

/-- The complete unique-index selector identity in (A.4) for arbitrary
finite-dimensional binary vector spaces. The index records both subspaces
and the genuine linear map with the required kernel and range. -/
theorem a4_unique_selector (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    (A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B) ↔
      ∃! p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨p, hp⟩ := a4_selector_exists Y A B ha hb
    exact ⟨p, hp, fun q hq => a4_surviving_index_unique Y A B q p hq hp⟩
  · rintro ⟨⟨A₀, B₀, X⟩, hp, _⟩
    rcases hp with ⟨_, _, inner, hk, hi, hr⟩
    exact a4_weak_selector_of_summand Y A₀ A B B₀ X inner hk hi hr

end UniqueGamesTheorem.Appendix.BinaryA4

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.evaluationCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixCharacters

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear

theorem tracePair_ext_right {n m : Nat} {S T : Matrix (Fin m) (Fin n) F2}
    (h : ∀ X, tracePair X S = tracePair X T) : S = T :=
  Matrix.ext_iff_trace_mul_left.mpr h

theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl
  · rfl
  · have hf : (1 : ℂ) = -1 := by simpa using h
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · have hf : (1 : ℂ) = -1 := by simpa using h.symm
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · rfl

theorem binarySign_real (a : F2) : ((binarySign a).re : ℂ) = binarySign a := by
  unfold binarySign
  split <;> simp

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_eq_matrix_tracePair {n m : Nat}
    (bE : Module.Basis (Fin m) F2 E) (bF : Module.Basis (Fin n) F2 F)
    (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S =
      tracePair (LinearMap.toMatrix bE bF X) (LinearMap.toMatrix bF bE S) := by
  change LinearMap.trace F2 F (X.comp S) =
    Matrix.trace (LinearMap.toMatrix bE bF X * LinearMap.toMatrix bF bE S)
  rw [LinearMap.trace_eq_matrix_trace F2 bF, LinearMap.toMatrix_comp bF bE bF]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_real (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    ((linearTraceCharacter S X).re : ℂ) = linearTraceCharacter S X := binarySign_real _

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem linearTracePair_swap (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S = linearTracePair S X :=
  LinearMap.trace_comp_comm' S X

theorem linearTraceCharacter_swap (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = linearTraceCharacter X S := by
  simp only [linearTraceCharacter_apply, linearTracePair_swap X S]

/-- The actual trace pairing is nondegenerate in its dual-map argument. -/
theorem linearTracePair_ext_right {S T : F →ₗ[F2] E}
    (h : ∀ X, linearTracePair X S = linearTracePair X T) : S = T := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  apply (LinearMap.toMatrix bF bE).injective
  apply tracePair_ext_right
  intro X
  obtain ⟨X', rfl⟩ := (LinearMap.toMatrix bE bF).surjective X
  exact (linearTracePair_eq_matrix_tracePair bE bF X' S).symm.trans
    ((h X').trans (linearTracePair_eq_matrix_tracePair bE bF X' T))

theorem linearTraceCharacter_injective :
    Function.Injective (linearTraceCharacter (E := E) (F := F)) := by
  intro S T h
  apply linearTracePair_ext_right
  intro X
  apply binarySign_injective
  exact congrArg (fun ψ : AddChar (E →ₗ[F2] F) ℂ => ψ X) h

theorem linearTraceCharacter_eq_zero_iff (S : F →ₗ[F2] E) :
    linearTraceCharacter S = 0 ↔ S = 0 := by
  rw [← linearTraceCharacter_zero, linearTraceCharacter_injective.eq_iff]

theorem sum_linearTraceCharacter [Fintype (E →ₗ[F2] F)] (S : F →ₗ[F2] E) :
    ∑ X, linearTraceCharacter S X =
      if S = 0 then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  simp only [linearTraceCharacter_eq_zero_iff]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixCharacters

end

end

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open UniqueGamesTheorem.Fourier.MatrixCharacters

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem card_linearMap_reverse :
    Fintype.card (F →ₗ[F2] E) = Fintype.card (E →ₗ[F2] F) := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  calc
    Fintype.card (F →ₗ[F2] E) =
        Fintype.card (Matrix (Fin (Module.finrank F2 E))
          (Fin (Module.finrank F2 F)) F2) :=
      Fintype.card_congr (LinearMap.toMatrix bF bE).toEquiv
    _ = Fintype.card (Matrix (Fin (Module.finrank F2 F))
          (Fin (Module.finrank F2 E)) F2) := by
      exact Fintype.card_congr
        { toFun := Matrix.transpose
          invFun := Matrix.transpose
          left_inv := Matrix.transpose_transpose
          right_inv := Matrix.transpose_transpose }
    _ = Fintype.card (E →ₗ[F2] F) :=
      (Fintype.card_congr (LinearMap.toMatrix bE bF).toEquiv).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearTraceCharacter_star (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    star (linearTraceCharacter S X) = linearTraceCharacter S X := by
  calc
    _ = star (((linearTraceCharacter S X).re : ℝ) : ℂ) :=
      congrArg star (linearTraceCharacter_real S X).symm
    _ = ((linearTraceCharacter S X).re : ℂ) := by simp
    _ = linearTraceCharacter S X := linearTraceCharacter_real S X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearMap_add_eq_zero_iff (X Y : E →ₗ[F2] F) :
    X + Y = 0 ↔ X = Y := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hself : Y + Y = 0 := by
    have h := congrArg (fun c : F2 => c • Y) htwo
    simpa only [add_smul, one_smul, zero_smul] using h
  have hneg : -Y = Y := neg_eq_iff_add_eq_zero.mpr hself
  rw [add_eq_zero_iff_eq_neg, hneg]

/-- Exact trace-character orthogonality with the frequency sum unnormalized. -/
theorem linear_character_kernel (X Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, star (linearTraceCharacter S X) * linearTraceCharacter S Y =
      if X = Y then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  calc
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter S (X + Y) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [linearTraceCharacter_star, AddChar.map_add_eq_mul]
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter (X + Y) S := by
      apply Finset.sum_congr rfl
      intro S _
      exact linearTraceCharacter_swap S (X + Y)
    _ = if X + Y = 0 then (Fintype.card (F →ₗ[F2] E) : ℂ) else 0 :=
      sum_linearTraceCharacter (X + Y)
    _ = _ := by rw [linearMap_add_eq_zero_iff, card_linearMap_reverse]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

/-- Fourier inversion obtained directly from the finite trace orthogonality sum. -/
theorem linear_complex_inversion (f : (E →ₗ[F2] F) → ℂ) (Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, fourierCoeff f (linearTraceCharacter S) *
      linearTraceCharacter S Y = f Y := by
  classical
  simp only [fourierCoeff]
  simp_rw [Finset.expect_mul, mul_assoc]
  rw [← Finset.expect_sum_comm]
  simp_rw [← Finset.mul_sum, linear_character_kernel]
  rw [Finset.expect_eq_sum_div_card]
  simp [mul_ite]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_complex (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    (linearCoeff f S : ℂ) =
      fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S) := by
  rw [linearCoeff, complex_ofReal_expect, fourierCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [Complex.ofReal_mul, linearTraceCharacter_real, linearTraceCharacter_star]

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.Derivatives
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linearCoeff_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector P f) Y = if P Y then linearCoeff f Y else 0 := by
  classical
  unfold spectralProjector
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem function_eq_of_linearCoeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ Y, linearCoeff f Y = linearCoeff g Y) : f = g := by
  funext M
  rw [← linear_fourier_inversion f M, ← linear_fourier_inversion g M]
  apply Finset.sum_congr rfl
  intro Y _
  rw [h Y]

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_OperatorPartitions
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual Fourier-projector partitions for Appendix A.4 and A.5

The partitions use the proved unique geometric selectors on each actual
Fourier index. Their finite index types are the canonical counting types.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix.Derivatives

namespace UniqueGamesTheorem.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

private theorem indicator_eq_sum_of_unique {I : Type*} [Fintype I]
    (P : Prop) (R : I → Prop) (a : ℝ)
    (hpart : P → ∃! i, R i) (hback : ∀ i, R i → P) :
    (if P then a else 0) = ∑ i, if R i then a else 0 := by
  classical
  by_cases hp : P
  · obtain ⟨i, hi, hu⟩ := hpart hp
    rw [ite_eq_left hp]
    symm
    calc
      (∑ j, if R j then a else 0) = if R i then a else 0 := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact ite_eq_right (fun hj => hji (hu j hj))
        · simp
      _ = a := ite_eq_left hi
  · rw [ite_eq_right hp]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hp (hback i hi))

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem spectralProjector_partition {I : Type*} [Fintype I]
    (P : (F →ₗ[F2] E) → Prop) (R : I → (F →ₗ[F2] E) → Prop)
    (hpart : ∀ Y, P Y → ∃! i, R i Y)
    (hback : ∀ i Y, R i Y → P Y) (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P f = ∑ i, spectralProjector (R i) f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  rw [linearCoeff_spectralProjector, linearCoeff_sum]
  simp only [linearCoeff_spectralProjector]
  exact indicator_eq_sum_of_unique (P Y) (fun i => R i Y)
    (linearCoeff f Y) (hpart Y) (fun i => hback i Y)

variable [Finite E] [Finite F]

open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a4Mask_unique (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (hY : A ≤ Y.range ∧ Y.ker ≤ B) :
    ∃! i : A4GeometricIndex A B, a4Mask A B i Y := by
  obtain ⟨p, hp, hu⟩ := (BinaryA4.a4_unique_selector Y A B).mp hY
  rcases hp with ⟨hA, hB, hinner, hker, hrange, hrank⟩
  let i : A4GeometricIndex A B := ⟨p, hA, hB, hker, hrange⟩
  refine ⟨i, ⟨hinner, hrank⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjA, hjB, hjker, hjrange⟩
  exact ⟨hjA, hjB, hj.1, hjker, hjrange, hj.2⟩

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a4Mask_implies_weak (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E)
    (hi : a4Mask A B i Y) : A ≤ Y.range ∧ Y.ker ≤ B := by
  rcases i.property with ⟨_, _, hker, hrange⟩
  exact a4_weak_selector_of_summand Y i.val.1 A B i.val.2.1 i.val.2.2
    hi.1 hker hrange hi.2

omit [Finite E] [Finite F] in
theorem a4_projector_partition (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f =
      ∑ i : A4GeometricIndex A B, spectralProjector (a4Mask A B i) f := by
  exact spectralProjector_partition _ _
    (a4Mask_unique A B) (a4Mask_implies_weak A B) f

end UniqueGamesTheorem.Appendix.OperatorPartitions

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

namespace UniqueGamesTheorem.Appendix.OperatorNorm

theorem energy_sum_sq_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 2) ^ 2 ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, (𝔼 n, g i n ^ 2) ^ 2 := by
  classical
  let e : I → ℝ := fun i => 𝔼 n, g i n ^ 2
  let E : ℝ := 𝔼 n, (∑ i, g i n) ^ 2
  let N : ℝ := Fintype.card I
  have hE : 0 ≤ E := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have he (i : I) : 0 ≤ e i := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hs : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he i
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp (n : Ω) : (∑ i, g i n) ^ 2 ≤ N * ∑ i, g i n ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) (fun i => g i n))
  have hEbound : E ≤ N * ∑ i, e i := by
    calc
      E ≤ 𝔼 n, N * ∑ i, g i n ^ 2 :=
        Finset.expect_le_expect fun n _ => hp n
      _ = N * ∑ i, e i := by
        rw [← Finset.mul_expect, Finset.expect_sum_comm]
  have hsq : E ^ 2 ≤ (N * ∑ i, e i) ^ 2 :=
    (sq_le_sq₀ hE (mul_nonneg hN hs)).mpr hEbound
  have hcs : (∑ i, e i) ^ 2 ≤ N * ∑ i, e i ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) e)
  change E ^ 2 ≤ N ^ 3 * ∑ i, e i ^ 2
  calc
    E ^ 2 ≤ N ^ 2 * (∑ i, e i) ^ 2 := by simpa [mul_pow] using hsq
    _ ≤ N ^ 2 * (N * ∑ i, e i ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg N)
    _ = N ^ 3 * ∑ i, e i ^ 2 := by ring

theorem fourth_sum_le_card_cube {I : Type*} [Fintype I] (a : I → ℝ) :
    (∑ i, a i) ^ 4 ≤ (Fintype.card I : ℝ) ^ 3 * ∑ i, a i ^ 4 := by
  have h := energy_sum_sq_le_card_cube (Ω := Unit) (fun i _ => a i)
  simpa [← pow_mul] using h

theorem average_fourth_sum_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
  calc
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
        𝔼 n, (Fintype.card I : ℝ) ^ 3 * ∑ i, g i n ^ 4 :=
      Finset.expect_le_expect fun n _ => fourth_sum_le_card_cube (fun i => g i n)
    _ = (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype
theorem a4_fourth_average_le_oai (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
      ∑ i : A4GeometricIndex A B,
        𝔼 T, 𝔼 N, mapDerivative i.val.2.2
          (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
  classical
  rw [a4_projector_partition A B f]
  simp only [Finset.sum_apply]
  calc
    (𝔼 M, (∑ i : A4GeometricIndex A B,
        spectralProjector (a4Mask A B i) f M) ^ 4) ≤
      (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B, 𝔼 M,
          spectralProjector (a4Mask A B i) f M ^ 4 :=
      average_fourth_sum_le_card_cube
        (fun (i : A4GeometricIndex A B) M => spectralProjector (a4Mask A B i) f M)
    _ = (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B,
          𝔼 T, 𝔼 N, mapDerivative i.val.2.2
            (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
      apply congrArg (fun r : ℝ =>
        (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      change (𝔼 M, spectralProjector
        (fun Y => Hybrid Y i.val.1 i.val.2.1 ∧
          RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)) f M ^ 4) = _
      exact (map_hybrid_fourth_average i.val.1 i.val.2.1 i.val.2.2 f).symm

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a4_fourth_average_le_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a4_fourth_average_le_oai.{u_1, u_2}
