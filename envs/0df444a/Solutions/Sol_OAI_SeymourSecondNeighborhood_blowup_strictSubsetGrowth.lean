-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.blowup_strictSubsetGrowth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:47:46.573008+00:00
-- url     : https://prove2.me/submissions/54dce309-bbd9-41dd-b90e-04240b655a3b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/TransitiveBlowup.lean:L136-L177
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.blowup_strictSubsetGrowth. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup

-- ---- from OAI.Combinatorics.SecondNeighborhood.TransitiveBlowup ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

variable [Fintype V] [DecidableEq V]

theorem blowup_mem_image_of_mem_base_image {r : V → V → Prop} {m : ℕ}
    (U : Finset (V × Fin m)) {p : V × Fin m}
    (hp : p.1 ∈ image r (U.image Prod.fst)) : p ∈ image (blowup r m) U := by
  classical
  obtain ⟨v, hv, hvp⟩ := mem_image.mp hp
  obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv
  apply mem_image.mpr
  refine ⟨q, hq, Or.inl ?_⟩
  simpa only [hqv] using hvp

theorem blowup_boundary_product_subset {r : V → V → Prop} {m : ℕ}
    (U : Finset (V × Fin m)) :
    (image r (U.image Prod.fst) \ U.image Prod.fst).product Finset.univ ⊆
      image (blowup r m) U \ U := by
  classical
  intro p hp
  obtain ⟨hpA, hpS⟩ := Finset.mem_sdiff.mp (Finset.mem_product.mp hp).1
  refine Finset.mem_sdiff.mpr ⟨blowup_mem_image_of_mem_base_image U hpA, ?_⟩
  intro hpU
  exact hpS (Finset.mem_image.mpr ⟨p, hpU, rfl⟩)

theorem blowup_second_sdiff_subset {r : V → V → Prop} {m : ℕ}
    (U : Finset (V × Fin m)) :
    image (blowup r m) (image (blowup r m) U) \ image (blowup r m) U ⊆
      (image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).product
        Finset.univ := by
  classical
  intro z hz
  obtain ⟨hzY, hzX⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨y, hyX, hyz⟩ := mem_image.mp hzY
  obtain ⟨x, hxU, hxy⟩ := mem_image.mp hyX
  have hxS : x.1 ∈ U.image Prod.fst := Finset.mem_image.mpr ⟨x, hxU, rfl⟩
  have hzA : z.1 ∉ image r (U.image Prod.fst) := by
    intro hzA
    exact hzX (blowup_mem_image_of_mem_base_image U hzA)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨?_, hzA⟩, Finset.mem_univ _⟩
  rcases hxy with hxy | ⟨hxy, hxylt⟩
  · rcases hyz with hyz | ⟨hyz, _⟩
    · exact mem_image.mpr ⟨y.1, mem_image.mpr ⟨x.1, hxS, hxy⟩, hyz⟩
    · exact False.elim (hzA (mem_image.mpr ⟨x.1, hxS, by
        simpa only [hyz] using hxy⟩))
  · rcases hyz with hyz | ⟨hyz, hyzlt⟩
    · exact False.elim (hzA (mem_image.mpr ⟨x.1, hxS, by
        simpa only [hxy] using hyz⟩))
    · apply False.elim
      apply hzX
      exact mem_image.mpr ⟨x, hxU, Or.inr ⟨hxy.trans hyz, lt_trans hxylt hyzlt⟩⟩

theorem blowup_fst_injOn_sdiff {r : V → V → Prop} {m : ℕ}
    (U : Finset (V × Fin m)) :
    Set.InjOn Prod.fst (↑(U \ image (blowup r m) U) : Set (V × Fin m)) := by
  classical
  intro p hp q hq hpq
  apply Prod.ext hpq
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · apply (Finset.mem_sdiff.mp hq).2
    exact mem_image.mpr ⟨p, (Finset.mem_sdiff.mp hp).1, Or.inr ⟨hpq, hij⟩⟩
  · apply (Finset.mem_sdiff.mp hp).2
    exact mem_image.mpr ⟨q, (Finset.mem_sdiff.mp hq).1, Or.inr ⟨hpq.symm, hij⟩⟩

theorem blowup_source_sdiff_card_le {r : V → V → Prop} {m : ℕ}
    (U : Finset (V × Fin m)) :
    (U \ image (blowup r m) U).card ≤ Fintype.card V := by
  classical
  have hcard : (U \ image (blowup r m) U).card ≤ (Finset.univ : Finset V).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact Finset.mem_univ _
    · exact blowup_fst_injOn_sdiff U
  simpa only [Finset.card_univ] using hcard

theorem card_add_card_lt_twice_of_sdiff {α : Type*} [DecidableEq α]
    (U X Y : Finset α)
    (h : (U \ X).card + (Y \ X).card < (X \ U).card) :
    U.card + Y.card < 2 * X.card := by
  have hUX := Finset.card_sdiff_add_card U X
  have hXU := Finset.card_sdiff_add_card X U
  rw [Finset.union_comm X U] at hXU
  have hY : Y.card ≤ (Y \ X).card + X.card :=
    Finset.card_le_card_sdiff_add_card
  omega

theorem blowup_image_eq_univ_of_full_support {r : V → V → Prop} {m : ℕ}
    (hi : PositiveIndegree r) (U : Finset (V × Fin m))
    (hS : U.image Prod.fst = Finset.univ) : image (blowup r m) U = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro p
  apply blowup_mem_image_of_mem_base_image U
  obtain ⟨v, hv⟩ := hi p.1
  apply mem_image.mpr
  refine ⟨v, ?_, hv⟩
  rw [hS]
  exact Finset.mem_univ _

theorem blowup_strictSubsetGrowth {r : V → V → Prop} {m : ℕ}
    (_hr : IsOriented r) (hi : PositiveIndegree r) (hd : SubsetDeficit r)
    (hm : Fintype.card V < m) : StrictSubsetGrowth (blowup r m) := by
  classical
  intro U hU hUproper
  by_cases hS : U.image Prod.fst = Finset.univ
  · have hX := blowup_image_eq_univ_of_full_support hi U hS
    have hUcard : U.card < (Finset.univ : Finset (V × Fin m)).card := by
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hUproper⟩
    have hYcard : (image (blowup r m) (image (blowup r m) U)).card ≤
        (Finset.univ : Finset (V × Fin m)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simp only [hX] at hYcard ⊢
    omega
  · have hSne : (U.image Prod.fst).Nonempty := by
      obtain ⟨p, hp⟩ := hU
      exact ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hdef := hd (U.image Prod.fst) hSne hS
    have hgain :
        (image (blowup r m) (image (blowup r m) U) \ image (blowup r m) U).card ≤
          (image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).card * m := by
      simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.card_le_card (blowup_second_sdiff_subset (r := r) U))
    have hloss :
        (image r (U.image Prod.fst) \ U.image Prod.fst).card * m ≤
          (image (blowup r m) U \ U).card := by
      simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.card_le_card (blowup_boundary_product_subset (r := r) U))
    have hsource := blowup_source_sdiff_card_le (r := r) U
    have hamp :
        (image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).card * m + m ≤
          (image r (U.image Prod.fst) \ U.image Prod.fst).card * m := by
      have hstep :
          ((image r (image r (U.image Prod.fst)) \ image r (U.image Prod.fst)).card + 1) * m ≤
            (image r (U.image Prod.fst) \ U.image Prod.fst).card * m :=
        Nat.mul_le_mul_right m (Nat.succ_le_of_lt hdef)
      simpa only [Nat.add_mul, Nat.one_mul] using hstep
    apply card_add_card_lt_twice_of_sdiff
    omega

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.blowup_strictSubsetGrowth := @_root_.OAI.SeymourSecondNeighborhood.blowup_strictSubsetGrowth
