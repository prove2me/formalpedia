-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a5_energySquare_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:32.749105+00:00
-- url     : https://prove2.me/submissions/8e2fb7a6-f15c-476d-8169-fed4df8af405

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
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_OperatorNorm_a5_summand_energy

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem quotient_rank_selected (A : Submodule K V) (Y : W →ₗ[K] V)
    (hA : A ≤ range Y) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at h
  exact h

omit [FiniteDimensional K V] in
theorem domain_rank_selected (B : Submodule K W) (Y : W →ₗ[K] V)
    (hB : ker Y ≤ B) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp, (Submodule.comapSubtypeEquivOfLe hB).finrank_eq] at h₁
  omega

omit [FiniteDimensional K V] in
theorem hybrid_rank_loss (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) (hA : A ≤ range Y) (hB : A.comap Y ≤ B) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have hquot := quotient_rank_selected A Y hA
  have hdom := domain_rank_selected B (A.mkQ.comp Y) (by
    simpa only [ker_comp, Submodule.ker_mkQ] using hB)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hdom
  omega

end UniqueGamesTheorem.Appendix.Level.LinearRank

end

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

theorem range_remainder_eq_range_on_kernel (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range (Y - X) = LinearMap.range (Y.domRestrict (LinearMap.ker X)) := by
  have hc := ((rankBelow_iff X Y).mp h).2
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    refine ⟨⟨k, hk⟩, ?_⟩
    change Y k = v
    calc
      Y k = (Y - X) k := by
        change Y k = Y k - X k
        rw [show X k = 0 from hk, sub_zero]
      _ = (Y - X) w := hzk
      _ = v := hw
  · rintro v ⟨w, hw⟩
    refine ⟨(w : W), ?_⟩
    change Y w - X w = v
    rw [show X w = 0 from w.property, sub_zero]
    exact hw

theorem mem_ker_of_apply_mem_range_remainder (X Y : W →ₗ[K] V)
    (h : RankBelow X Y) (w : W) (hw : Y w ∈ LinearMap.range (Y - X)) :
    w ∈ LinearMap.ker X := by
  have hd := ((rankBelow_iff X Y).mp h).1
  have hz : (Y - X) w ∈ LinearMap.range (Y - X) := ⟨w, rfl⟩
  have hx : X w ∈ LinearMap.range (Y - X) := by
    have hs := (LinearMap.range (Y - X)).sub_mem hw hz
    have heq : Y w - (Y - X) w = X w := by
      simp only [LinearMap.sub_apply]
      abel
    exact heq ▸ hs
  exact Submodule.disjoint_def.mp hd (X w) ⟨w, rfl⟩ hx

end UniqueGamesTheorem.Appendix.RankAdditivity

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_Identities
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

theorem compress_sub (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    compress (Y - X) A B = compress Y A B - compress X A B := by
  ext b
  simp only [compress_apply, LinearMap.sub_apply, map_sub]

theorem quotient_mem_image_iff (A₀ A : Submodule K V) (hA : A₀ ≤ A) (v : V) :
    A₀.mkQ v ∈ A.map A₀.mkQ ↔ v ∈ A := by
  change v ∈ (A.map A₀.mkQ).comap A₀.mkQ ↔ v ∈ A
  rw [Submodule.comap_map_mkQ, sup_of_le_right hA]

variable [FiniteDimensional K W]

/-- Compression preserves the full rank when its quotient is disjoint
from the image and its restricted domain spans the domain modulo the kernel. -/
theorem compress_rank_preserved (X : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hdis : Disjoint A (LinearMap.range X))
    (hcover : B ⊔ LinearMap.ker X = ⊤) :
    Module.finrank K (LinearMap.range (compress X A B)) =
      Module.finrank K (LinearMap.range X) := by
  have hrestrict : LinearMap.range (X.domRestrict B) = LinearMap.range X := by
    apply le_antisymm (LinearMap.range_domRestrict_le_range X B)
    intro v hv
    rcases hv with ⟨w, hw⟩
    have hwtop : w ∈ B ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    change X b = v
    rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]
  have h := (A.mkQ.comp (LinearMap.range X).subtype).finrank_range_add_finrank_ker
  have hr : LinearMap.range (A.mkQ.comp (LinearMap.range X).subtype) =
      LinearMap.range (compress X A B) := by
    simp only [compress, LinearMap.range_comp, Submodule.range_subtype, hrestrict]
  rw [hr, LinearMap.ker_comp, Submodule.ker_mkQ,
    Submodule.disjoint_iff_comap_eq_bot.mp hdis.symm] at h
  simpa using h

/-- The reverse summand of (A.5) really satisfies the hybrid selector for
the remainder `Y - X`. The hypotheses here are exactly the inner hybrid
selector, complement conditions, and the compressed rank-order selector.
No image-lifting or disjointness conclusion is assumed separately. -/
theorem reverse_hybrid_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (Y - X) A₀ B₀ := by
  have hker := RankAdditivity.ker_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  have himg := RankAdditivity.range_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hxA : X w ∈ A₀ := by
      have hx : X w ∈ LinearMap.ker A₀.mkQ := hker hwy
      simpa only [Submodule.ker_mkQ] using hx
    have hx : X w = 0 := Submodule.disjoint_def.mp hdis (X w) hxA ⟨w, rfl⟩
    exact ⟨w, by change Y w - X w = a; rw [hw, hx, sub_zero]⟩
  · intro w hw
    have hwZ : Y w - X w ∈ A₀ := hw
    have hwtop : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    have hxb : X b = X w := by
      rw [← hbk, map_add, show X k = 0 from hk, add_zero]
    have hxran : compress X A₀ B₀ ⟨b, hb⟩ ∈ LinearMap.range (compress X A₀ B₀) :=
      ⟨⟨b, hb⟩, rfl⟩
    rcases himg hxran with ⟨c, hc⟩
    have hdiff : X w - Y c ∈ A₀ := by
      rw [← hxb]
      exact (Submodule.Quotient.eq A₀).mp hc.symm
    have hsum : Y (w - c) ∈ A₀ := by
      have h := A₀.add_mem hwZ hdiff
      have heq : (Y w - X w) + (X w - Y c) = Y (w - c) := by rw [map_sub]; abel
      exact heq ▸ h
    have hwc : w - c ∈ B₀ := inner.2 hsum
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

/-- A surviving right-hand summand of (A.5) forces the original rank
order `X ⪯ Y`. This lifts the local rank equation using the two actual
hybrid rank-loss equalities, so it does not assume global rank additivity. -/
theorem rankBelow_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    RankAdditivity.RankBelow X Y := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y inner.1 inner.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) remainder.1 remainder.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  have hloc : Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
      Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
      Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) := by
    rw [compress_sub]
    exact hlocal
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X))
  omega

/-- The complement in the codomain is forced by the remainder image. -/
theorem image_inter_complement_eq (A₀ I J : Submodule K V)
    (hA : A₀ ≤ J) (hdis : Disjoint I J) : J ⊓ (A₀ ⊔ I) = A₀ := by
  apply le_antisymm
  · intro v hv
    rcases Submodule.mem_sup.mp hv.2 with ⟨a, ha, i, hi, hai⟩
    have hiJ : i ∈ J := by
      have h := J.sub_mem hv.1 (hA ha)
      have heq : v - a = i := by rw [← hai]; abel
      exact heq ▸ h
    have hi0 := Submodule.disjoint_def.mp hdis i hi hiJ
    rw [hi0, add_zero] at hai
    exact hai ▸ ha
  · intro a ha
    exact ⟨hA ha, (show A₀ ≤ A₀ ⊔ I from le_sup_left) ha⟩

omit [FiniteDimensional K W] in
/-- The complement in the domain is forced by the remainder kernel. -/
theorem domain_complement_eq (B₀ K₀ J : Submodule K W)
    (hJ : J ≤ B₀) (hcover : K₀ ⊔ J = ⊤) : B₀ = (B₀ ⊓ K₀) ⊔ J := by
  apply le_antisymm
  · intro w hw
    have hwtop : w ∈ K₀ ⊔ J := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨k, hk, j, hj, hkj⟩
    have hkB : k ∈ B₀ := by
      have h := B₀.sub_mem hw (hJ hj)
      have heq : w - j = k := by rw [← hkj]; abel
      exact heq ▸ h
    exact Submodule.mem_sup.mpr ⟨k, ⟨hkB, hk⟩, j, hj, hkj⟩
  · exact sup_le inf_le_left hJ

/-- Every surviving right-hand pair in (A.5) is the displayed canonical pair. -/
theorem surviving_pair_forced (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    A₀ = LinearMap.range (Y - X) ⊓ A ∧ B₀ = B ⊔ LinearMap.ker (Y - X) := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have global := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have geometry := (RankAdditivity.rankBelow_iff X Y).mp global
  constructor
  · have h := image_inter_complement_eq A₀ (LinearMap.range X)
      (LinearMap.range (Y - X)) remainder.1 geometry.1
    rw [hA] at h
    exact h.symm
  · have hker : LinearMap.ker (Y - X) ≤ B₀ := by
      intro w hw
      apply remainder.2
      change (Y - X) w ∈ A₀
      rw [show (Y - X) w = 0 from hw]
      exact A₀.zero_mem
    have h := domain_complement_eq B₀ (LinearMap.ker X) (LinearMap.ker (Y - X)) hker geometry.2
    rw [hB] at h
    exact h

theorem canonical_inner_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid Y (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · have hz : LinearMap.range (Y - X) ≤ LinearMap.range Y := by
      rw [RankAdditivity.range_remainder_eq_range_on_kernel X Y hrank]
      exact LinearMap.range_domRestrict_le_range Y (LinearMap.ker X)
    exact inf_le_left.trans hz
  · intro w hw
    have hy : Y w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hk : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hrank w hy.1
    have hq : (⟨w, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y w, hy.2, rfl⟩
    have hb : w ∈ B := outer.2 hq
    exact (show B ≤ B ⊔ LinearMap.ker (Y - X) from le_sup_left) hb

theorem canonical_remainder_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid (Y - X) (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · exact inf_le_left
  · intro w hw
    have hwZ : (Y - X) w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    have hyk : Y k = (Y - X) w := by
      calc
        Y k = (Y - X) k := by
          change Y k = Y k - X k
          rw [show X k = 0 from hk, sub_zero]
        _ = (Y - X) w := hzk
    have hyA : Y k ∈ A := by rw [hyk]; exact hwZ.2
    have hq : (⟨k, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y k, hyA, rfl⟩
    have hkB : k ∈ B := outer.2 hq
    exact Submodule.mem_sup.mpr ⟨k, hkB, j, hj, hkj⟩

theorem canonical_codomain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Disjoint (LinearMap.range (Y - X) ⊓ A) (LinearMap.range X) ∧
      (LinearMap.range (Y - X) ⊓ A) ⊔ LinearMap.range X = A := by
  have hd := ((RankAdditivity.rankBelow_iff X Y).mp hrank).1
  refine ⟨hd.symm.mono_left inf_le_left, ?_⟩
  apply le_antisymm (sup_le inf_le_right hI)
  intro a ha
  have hqa : (LinearMap.range X).mkQ a ∈ A.map (LinearMap.range X).mkQ := ⟨a, ha, rfl⟩
  rcases outer.1 hqa with ⟨k, hk⟩
  have hi : a - Y k ∈ LinearMap.range X :=
    (Submodule.Quotient.eq (LinearMap.range X)).mp hk.symm
  have hyA : Y k ∈ A := by
    have h := A.sub_mem ha (hI hi)
    have heq : a - (a - Y k) = Y k := by abel
    exact heq ▸ h
  have hyZ : Y k ∈ LinearMap.range (Y - X) :=
    ⟨(k : W), by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]⟩
  exact Submodule.mem_sup.mpr ⟨Y k, ⟨hyZ, hyA⟩, a - Y k, hi, by abel⟩

theorem canonical_domain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hB : B ≤ LinearMap.ker X) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    (B ⊔ LinearMap.ker (Y - X)) ⊓ LinearMap.ker X = B ∧
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X = ⊤ := by
  constructor
  · apply le_antisymm
    · intro w hw
      rcases Submodule.mem_sup.mp hw.1 with ⟨b, hb, j, hj, hbj⟩
      have hjK : j ∈ LinearMap.ker X := by
        have h := (LinearMap.ker X).sub_mem hw.2 (hB hb)
        have heq : w - b = j := by rw [← hbj]; abel
        exact heq ▸ h
      have hyj : Y j = 0 := by
        have hz : Y j - X j = 0 := hj
        rw [show X j = 0 from hjK, sub_zero] at hz
        exact hz
      have hq : (⟨j, hjK⟩ : LinearMap.ker X) ∈
          (A.map (LinearMap.range X).mkQ).comap
            (compress Y (LinearMap.range X) (LinearMap.ker X)) := by
        change (LinearMap.range X).mkQ (Y j) ∈ A.map (LinearMap.range X).mkQ
        rw [hyj, map_zero]
        exact Submodule.zero_mem _
      have hjB : j ∈ B := outer.2 hq
      have h := B.add_mem hb hjB
      exact hbj ▸ h
    · exact le_inf le_sup_left hB
  · have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    calc
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X =
        B ⊔ (LinearMap.ker X ⊔ LinearMap.ker (Y - X)) := by ac_rfl
      _ = ⊤ := by rw [hc, sup_top_eq]

theorem compressed_rankBelow_of_hybrids (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (hy : Hybrid Y A₀ B₀) (hz : Hybrid (Y - X) A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hrank : RankAdditivity.RankBelow X Y) :
    RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀) := by
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y hy.1 hy.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) hz.1 hz.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X)) at hrank
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
    Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
    Module.finrank K (LinearMap.range (compress Y A₀ B₀ - compress X A₀ B₀))
  rw [← compress_sub]
  omega

theorem reverse_outer_hybrid (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype) := by
  have hg := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hz := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hf := surviving_pair_forced X Y A₀ A B B₀ inner hdis hA hcover hB hlocal
  have hI : LinearMap.range X ≤ A := by rw [← hA]; exact le_sup_right
  constructor
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    have haSum : a ∈ A₀ ⊔ LinearMap.range X := by rw [hA]; exact ha
    rcases Submodule.mem_sup.mp haSum with ⟨a₀, ha₀, i, hi, hai⟩
    rcases inner.1 ha₀ with ⟨w, hw⟩
    have hyZ : Y w ∈ LinearMap.range (Y - X) := by rw [hw]; exact hz.1 ha₀
    have hwK : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hg w hyZ
    refine ⟨⟨w, hwK⟩, ?_⟩
    have hqi : (LinearMap.range X).mkQ i = 0 := by
      change i ∈ LinearMap.ker (LinearMap.range X).mkQ
      rw [Submodule.ker_mkQ]
      exact hi
    change (LinearMap.range X).mkQ (Y w) = (LinearMap.range X).mkQ a
    rw [hw, ← hai, map_add, hqi, add_zero]
  · intro k hk
    have hyA : Y k ∈ A :=
      (quotient_mem_image_iff (LinearMap.range X) A hI (Y k)).mp hk
    have hZk : (Y - X) k = Y k := by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]
    have hyZ : Y k ∈ LinearMap.range (Y - X) := ⟨(k : W), hZk⟩
    have ha₀ : Y k ∈ A₀ := by rw [hf.1]; exact ⟨hyZ, hyA⟩
    have hkB₀ : (k : W) ∈ B₀ := hz.2 (by
      change (Y - X) k ∈ A₀
      rw [hZk]
      exact ha₀)
    change (k : W) ∈ B
    rw [← hB]
    exact ⟨hkB₀, k.property⟩

/-- The complete unique-summand selector identity in (A.5), in arbitrary
finite dimensions. In characteristic two the remainder `Y-X` is `Y+X`. -/
theorem a5_unique_selector (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hB : B ≤ LinearMap.ker X) :
    (RankAdditivity.RankBelow X Y ∧
      Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
        (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) ↔
      ∃! p : Submodule K V × Submodule K W, A5PairSurvives X Y A B p := by
  constructor
  · rintro ⟨hr, ho⟩
    have hy := canonical_inner_hybrid X Y A B hr ho
    have hz := canonical_remainder_hybrid X Y A B hr ho
    have ha := canonical_codomain_complement X Y A B hI hr ho
    have hb := canonical_domain_complement X Y A B hB hr ho
    have hl := compressed_rankBelow_of_hybrids X Y
      (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) hy hz ha.1 hb.2 hr
    refine ⟨(LinearMap.range (Y - X) ⊓ A, B ⊔ LinearMap.ker (Y - X)),
      ⟨hy, ha.1, ha.2, hb.2, hb.1, hl⟩, ?_⟩
    rintro ⟨A₀, B₀⟩ hp
    rcases hp with ⟨hi, hd, ha', hc, hb', hl'⟩
    have hf := surviving_pair_forced X Y A₀ A B B₀ hi hd ha' hc hb' hl'
    exact Prod.ext hf.1 hf.2
  · rintro ⟨⟨A₀, B₀⟩, hp, _⟩
    rcases hp with ⟨hi, hd, ha, hc, hb, hl⟩
    exact ⟨rankBelow_of_compressed_rankBelow X Y A₀ B₀ hi hd hc hl,
      reverse_outer_hybrid X Y A₀ A B B₀ hi hd ha hc hb hl⟩

/-! ## The unique selector in (A.4) -/

end UniqueGamesTheorem.Appendix.LinearIdentities

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
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.outputFactor_val _root_.OAI.UniqueGamesTheorem.Appendix.NaturalTransport.quotientFactor_mkQ _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Appendix.Restriction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

section ActualRestrictions

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- Trace compatibility on the actual quotient restriction. -/
theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair UniqueGamesTheorem.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in
/-- The complex character identity in (A.1), on actual binary linear maps. -/
theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro Y _
    rw [real_character_restriction]
    ring
  rw [hexpansion, linearCoeff_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_smul, linearCoeff_character]
  by_cases h : compressFrequency A B Y = Z
  · simp [h]
  · simp [h, Ne.symm h]

end ActualRestrictions

end UniqueGamesTheorem.Appendix.Restriction

end

end

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

theorem spectralProjector_comp (P Q : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P (spectralProjector Q f) =
      spectralProjector (fun Y => P Y ∧ Q Y) f := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [linearCoeff_spectralProjector]
  by_cases hP : P Y <;> by_cases hQ : Q Y <;> simp [hP, hQ]

variable [Finite E] [Finite F]

theorem spectralProjector_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (T : E →ₗ[F2] F) :
    spectralProjector Q (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
        (spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f) A B T := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Z
  rw [linearCoeff_spectralProjector,
    Restriction.linear_coefficient_merging, Restriction.linear_coefficient_merging]
  by_cases hQ : Q Z
  · simp only [ite_eq_left hQ]
    apply Finset.sum_congr rfl
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]
  · simp only [ite_eq_right hQ]
    symm
    apply Finset.sum_eq_zero
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]

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

theorem spectralProjector_restriction_projector
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (P : (F →ₗ[F2] E) → Prop)
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    spectralProjector Q
      (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict (spectralProjector P f) A B T) =
    UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
      (spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f)
      A B T := by
  have hp : (fun Y => Q (Restriction.compressFrequency A B Y) ∧ P Y) =
      (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) := by
    funext Y
    exact propext and_comm
  rw [spectralProjector_restriction, spectralProjector_comp, hp]

open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a5Mask_unique (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (Y : F →ₗ[F2] E) (hY : a5OuterMask X A B Y) :
    ∃! i : A5GeometricIndex X A B, a5Mask X A B i Y := by
  obtain ⟨p, hp, hu⟩ := (a5_unique_selector X Y A B hI hB).mp hY
  rcases hp with ⟨hinner, hdis, hA, hcover, hmeet, hlocal⟩
  let i : A5GeometricIndex X A B := ⟨p, hdis, hA, hcover, hmeet⟩
  refine ⟨i, ⟨hinner, hlocal⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjdis, hjA, hjcover, hjmeet⟩
  exact ⟨hj.1, hjdis, hjA, hjcover, hjmeet, hj.2⟩

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a5Mask_implies_outer (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B) (Y : F →ₗ[F2] E)
    (hi : a5Mask X A B i Y) : a5OuterMask X A B Y := by
  rcases i.property with ⟨hdis, hA, hcover, hmeet⟩
  exact ⟨rankBelow_of_compressed_rankBelow X Y i.val.1 i.val.2
      hi.1 hdis hcover hi.2,
    reverse_outer_hybrid X Y i.val.1 A B i.val.2
      hi.1 hdis hA hcover hmeet hi.2⟩

omit [Finite E] [Finite F] in
theorem a5_projector_partition (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (a5OuterMask X A B) f =
      ∑ i : A5GeometricIndex X A B, spectralProjector (a5Mask X A B i) f := by
  exact spectralProjector_partition _ _
    (a5Mask_unique X A B hI hB) (a5Mask_implies_outer X A B) f

end UniqueGamesTheorem.Appendix.OperatorPartitions

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionTransport
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

namespace Appendix.RestrictionTransport

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem nestedEmbedding_injective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Function.Injective (nestedEmbedding A B C D) := by
  intro N N' h
  apply embed_injective C D
  apply embed_injective A B
  exact h

/-- Exact effective annihilator and target of a nested restriction. -/
theorem exists_nested_embed_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (M : E →ₗ[F2] F) :
    (∃ N : Parameter C D, nestedEmbedding A B C D N = M) ↔
      C.comap A.mkQ ≤ M.ker ∧ M.range ≤ D.map B.subtype := by
  constructor
  · rintro ⟨N, rfl⟩
    constructor
    · intro x hx
      change (embed C D N (A.mkQ x) : F) = 0
      have hz : embed C D N (A.mkQ x) = 0 := embed_vanishes C D N hx
      rw [hz]
      rfl
    · rintro y ⟨x, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨embed C D N (A.mkQ x), ?_, rfl⟩
      exact embed_range C D N ⟨A.mkQ x, rfl⟩
  · rintro ⟨hker, hrange⟩
    have hA : A ≤ M.ker := by
      intro x hx
      apply hker
      change A.mkQ x ∈ C
      have hz : A.mkQ x = 0 := by simpa using hx
      rw [hz]
      exact C.zero_mem
    have hB : M.range ≤ B := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp (hrange hy)
      exact b.property
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr ⟨hA, hB⟩
    have hC : C ≤ N.ker := by
      intro q hq
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      change N (A.mkQ x) = 0
      apply Subtype.ext
      change embed A B N x = 0
      rw [hN]
      exact hker hq
    have hD : N.range ≤ D := by
      rintro b ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      have hm : M x ∈ D.map B.subtype := hrange ⟨x, rfl⟩
      have hco : (N (A.mkQ x) : F) = M x := congrArg (fun L : E →ₗ[F2] F => L x) hN
      rw [← hco] at hm
      obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hm
      have heq' : b = N (A.mkQ x) := Subtype.ext heq
      exact heq' ▸ hb
    obtain ⟨P, hP⟩ := (exists_embed_iff C D N).mpr ⟨hC, hD⟩
    refine ⟨P, ?_⟩
    change embed A B (embed C D P) = M
    rw [hP, hN]

/-- Nested and effective direct restrictions describe exactly the same perturbations. -/
theorem nested_range_eq (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (nestedEmbedding A B C D).range =
      (embedding (C.comap A.mkQ) (D.map B.subtype)).range := by
  ext M
  change (∃ N, nestedEmbedding A B C D N = M) ↔
    (∃ N, embed (C.comap A.mkQ) (D.map B.subtype) N = M)
  rw [exists_nested_embed_iff, exists_embed_iff]

end Nested

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

theorem sameRangeEquiv_commutes (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (x : P) :
    g (sameRangeEquiv f g hf hg h x) = f x := by
  exact Classical.choose_spec (exists_range_preimage f g (le_of_eq h) x)

variable [Fintype P] [Fintype Q]

/-- Injective parameter changes preserve normalized uniform expectations. -/
theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

/-- Preserve second moments at the same full ambient translate. -/
theorem restriction_secondMoment_eq_of_same_range
    (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) (T : G) :
    (𝔼 x, observable (T + f x) ^ 2) = 𝔼 y, observable (T + g y) ^ 2 :=
  expect_eq_of_same_range f g hf hg h (fun z => observable (T + z) ^ 2)

end SameRange

end Appendix.RestrictionTransport

end

end UniqueGamesTheorem

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

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem compressFrequency_eq_compress (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : Restriction.compressFrequency A B Y = compress Y A B := by
  ext x
  rfl

theorem nested_projector_restriction_apply
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (P : (F →ₗ[F2] E) → Prop) (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F)
    (S : MatrixRestrictions.Parameter A B) (N : MatrixRestrictions.Parameter C D) :
    MatrixRestrictions.restrict
      (spectralProjector Q (MatrixRestrictions.restrict (spectralProjector P f) A B T))
      C D S N =
    spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
      (T + MatrixRestrictions.embed A B S + RestrictionTransport.nestedEmbedding A B C D N) := by
  classical
  rw [OperatorPartitions.spectralProjector_restriction_projector]
  let g := spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
  change g (T + (MatrixRestrictions.embedding A B)
      (S + MatrixRestrictions.embed C D N)) =
    g ((T + (MatrixRestrictions.embedding A B) S) +
      (MatrixRestrictions.embedding A B) (MatrixRestrictions.embed C D N))
  rw [map_add, add_assoc]

theorem a5_outer_energy (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) =
    𝔼 M : MatrixRestrictions.Parameter A B,
      spectralProjector (a5OuterMask X A B) f
        (MatrixRestrictions.embed X.range X.ker S + MatrixRestrictions.embed A B M) ^ 2 := by
  classical
  let C := A.map X.range.mkQ
  let D := B.comap X.ker.subtype
  let g := spectralProjector (a5OuterMask X A B) f
  let t := MatrixRestrictions.embed X.range X.ker S
  have hp (N : MatrixRestrictions.Parameter C D) :
      hybridDerivative C D S (mapDerivative X f) N =
        g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) := by
    have hm : (fun Y => RankBelow X Y ∧ Hybrid (compress Y X.range X.ker) C D) =
        a5OuterMask X A B := rfl
    have hh := nested_projector_restriction_apply X.range X.ker C D
      (fun Y => RankBelow X Y) (fun Y => Hybrid Y C D) f 0 S N
    simp only [compressFrequency_eq_compress] at hh
    rw [hm] at hh
    simpa only [hybridDerivative, hybridProjector, mapDerivative, rankProjector,
      g, t, zero_add] using hh
  calc
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) =
        𝔼 N, g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) ^ 2 :=
      Finset.expect_congr rfl fun N _ => congrArg (fun r : ℝ => r ^ 2) (hp N)
    _ = 𝔼 M : MatrixRestrictions.Parameter A B,
        g (t + MatrixRestrictions.embed A B M) ^ 2 := by
      have ha : C.comap X.range.mkQ = A := by
        dsimp only [C]
        rw [Submodule.comap_map_mkQ, sup_of_le_right hI]
      have hb : D.map X.ker.subtype = B := by
        dsimp only [D]
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr hB]
      have hrange : (RestrictionTransport.nestedEmbedding X.range X.ker C D).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq, ha, hb]
      have htransport := RestrictionTransport.restriction_secondMoment_eq_of_same_range
        (K := F2) (P := MatrixRestrictions.Parameter C D)
        (Q := MatrixRestrictions.Parameter A B) (G := E →ₗ[F2] F)
        (RestrictionTransport.nestedEmbedding X.range X.ker C D)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective X.range X.ker C D)
        (MatrixRestrictions.embed_injective A B) hrange g t
      simpa only [MatrixRestrictions.embedding, LinearMap.coe_mk, AddHom.coe_mk] using htransport

theorem a5_energySquare_le_oai (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)]
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) ^ 2 ≤
    (Fintype.card (A5GeometricIndex X A B) : ℝ) ^ 3 *
      ∑ i : A5GeometricIndex X A B,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2
            (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) ^ 2 := by
  classical
  let J := A5GeometricIndex X A B
  let t := MatrixRestrictions.embed X.range X.ker S
  let g : J → MatrixRestrictions.Parameter A B → ℝ := fun i M =>
    spectralProjector (a5Mask X A B i) f (t + MatrixRestrictions.embed A B M)
  have hp (M : MatrixRestrictions.Parameter A B) :
      spectralProjector (a5OuterMask X A B) f
        (t + MatrixRestrictions.embed A B M) = ∑ i : J, g i M := by
    have h := congrFun (a5_projector_partition X A B hI hB f)
      (t + MatrixRestrictions.embed A B M)
    simpa only [Finset.sum_apply, g] using h
  have ho :
      (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
        S (mapDerivative X f) N ^ 2) = 𝔼 M, (∑ i : J, g i M) ^ 2 := by
    rw [a5_outer_energy X A B hI hB f S]
    exact Finset.expect_congr rfl fun M _ => congrArg (fun r : ℝ => r ^ 2) (hp M)
  have hi (i : J) :
      (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
        (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) = 𝔼 M, g i M ^ 2 :=
    a5_summand_energy X A B i f S
  rw [ho]
  calc
    (𝔼 M, (∑ i : J, g i M) ^ 2) ^ 2 ≤
        (Fintype.card J : ℝ) ^ 3 * ∑ i : J, (𝔼 M, g i M ^ 2) ^ 2 :=
      energy_sum_sq_le_card_cube g
    _ = (Fintype.card J : ℝ) ^ 3 * ∑ i : J,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) ^ 2 := by
      apply congrArg (fun r : ℝ => (Fintype.card J : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r : ℝ => r ^ 2) (hi i).symm

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a5_energySquare_le_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.OperatorNorm.a5_energySquare_le_oai.{u_1, u_2}
