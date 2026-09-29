-- Prove2me | solution 1 for M4aLocalCFT.fieldUnitsDecomp_herbrandQuotient_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a2d54cc7-07e3-58ae-be90-6a9f10a07a80

import Definitions.Def_M4aLocalCFT_VocabDefs
import Theorems.Thm_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card

set_option autoImplicit false

namespace M4aLocalCFT
p2m_export "M4aLocalCFT" "unitsAct unitsNorm unitsDerive fieldUnitsAct fieldUnitsNorm fieldUnitsDerive unitsDecomp_herbrandQuotient_eq_one"
p2m_open "M4aLocalCFT"
namespace FieldUnitsHerbrandReduction

section ExactCycle

theorem nat_card_eq_card_range_mul_card_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) : Nat.card G = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

variable {G₀ G₁ G₂ G₃ G₄ G₅ : Type*}
  [Group G₀] [Group G₁] [Group G₂] [Group G₃] [Group G₄] [Group G₅]

theorem card_mul_eq_of_exactCycle
    (f₀ : G₀ →* G₁) (f₁ : G₁ →* G₂) (f₂ : G₂ →* G₃)
    (f₃ : G₃ →* G₄) (f₄ : G₄ →* G₅) (f₅ : G₅ →* G₀)
    (h₀ : f₀.range = f₁.ker) (h₁ : f₁.range = f₂.ker) (h₂ : f₂.range = f₃.ker)
    (h₃ : f₃.range = f₄.ker) (h₄ : f₄.range = f₅.ker) (h₅ : f₅.range = f₀.ker) :
    Nat.card G₀ * Nat.card G₂ * Nat.card G₄ =
      Nat.card G₁ * Nat.card G₃ * Nat.card G₅ := by
  have e₀ : Nat.card G₀ = Nat.card f₀.range * Nat.card f₅.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₀, ← h₅]
  have e₁ : Nat.card G₁ = Nat.card f₁.range * Nat.card f₀.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₁, ← h₀]
  have e₂ : Nat.card G₂ = Nat.card f₂.range * Nat.card f₁.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₂, ← h₁]
  have e₃ : Nat.card G₃ = Nat.card f₃.range * Nat.card f₂.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₃, ← h₂]
  have e₄ : Nat.card G₄ = Nat.card f₄.range * Nat.card f₃.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₄, ← h₃]
  have e₅ : Nat.card G₅ = Nat.card f₅.range * Nat.card f₄.range := by
    rw [nat_card_eq_card_range_mul_card_ker f₅, ← h₄]
  rw [e₀, e₁, e₂, e₃, e₄, e₅]
  ring

end ExactCycle

structure MPair (A : Type*) [CommGroup A] where

  derive : A →* A

  norm : A →* A
  derive_norm : ∀ a, derive (norm a) = 1
  norm_derive : ∀ a, norm (derive a) = 1

namespace MPair

variable {A : Type*} [CommGroup A] (P : MPair A)

abbrev Tate0 : Type _ := P.derive.ker ⧸ P.norm.range.subgroupOf P.derive.ker

abbrev Tate1 : Type _ := P.norm.ker ⧸ P.derive.range.subgroupOf P.norm.ker

noncomputable def tateCard₀ : ℕ := Nat.card P.Tate0

noncomputable def tateCard₁ : ℕ := Nat.card P.Tate1

def swap : MPair A where
  derive := P.norm
  norm := P.derive
  derive_norm := P.norm_derive
  norm_derive := P.derive_norm

theorem tateCard₀_swap : P.swap.tateCard₀ = P.tateCard₁ := rfl

theorem tateCard₁_swap : P.swap.tateCard₁ = P.tateCard₀ := rfl

end MPair

theorem tateQuot_mk_eq_mk {α : Type*} [CommGroup α] {K S : Subgroup α} (x y : K) :
    (QuotientGroup.mk x : K ⧸ S.subgroupOf K) = QuotientGroup.mk y ↔ (x : α) / y ∈ S := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have : ((x⁻¹ * y : K) : α) = ((x : α) / y)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_div, div_eq_mul_inv, mul_comm]
  rw [this, S.inv_mem_iff]

theorem tateQuot_mk_eq_one {α : Type*} [CommGroup α] {K S : Subgroup α} (x : K) :
    (QuotientGroup.mk x : K ⧸ S.subgroupOf K) = 1 ↔ (x : α) ∈ S := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

structure MTriple (A B C : Type*) [CommGroup A] [CommGroup B] [CommGroup C] where
  P : MPair A
  Q : MPair B
  R : MPair C
  ι : A →* B
  π : B →* C
  ι_injective : Function.Injective ι
  π_surjective : Function.Surjective π
  exact : ι.range = π.ker
  derive_ι : ∀ a, Q.derive (ι a) = ι (P.derive a)
  norm_ι : ∀ a, Q.norm (ι a) = ι (P.norm a)
  derive_π : ∀ b, R.derive (π b) = π (Q.derive b)
  norm_π : ∀ b, R.norm (π b) = π (Q.norm b)

namespace MTriple

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
variable (T : MTriple A B C)

def swap : MTriple A B C where
  P := T.P.swap
  Q := T.Q.swap
  R := T.R.swap
  ι := T.ι
  π := T.π
  ι_injective := T.ι_injective
  π_surjective := T.π_surjective
  exact := T.exact
  derive_ι := T.norm_ι
  norm_ι := T.derive_ι
  derive_π := T.norm_π
  norm_π := T.derive_π

theorem exists_of_π_eq_one {b : B} (hb : T.π b = 1) : ∃ a, T.ι a = b := by
  have : b ∈ T.π.ker := hb
  rw [← T.exact] at this
  exact this

theorem π_ι (a : A) : T.π (T.ι a) = 1 := by
  have h : T.ι a ∈ T.ι.range := ⟨a, rfl⟩
  rw [T.exact] at h
  exact h

def ιKer : T.P.derive.ker →* T.Q.derive.ker where
  toFun a := ⟨T.ι a.1, by
    rw [MonoidHom.mem_ker, T.derive_ι, MonoidHom.mem_ker.mp a.2, map_one]⟩
  map_one' := Subtype.ext (map_one T.ι)
  map_mul' a b := Subtype.ext (map_mul T.ι a.1 b.1)

@[scoped simp] theorem ιKer_coe (a : T.P.derive.ker) : (T.ιKer a : B) = T.ι a.1 := rfl

def πKer : T.Q.derive.ker →* T.R.derive.ker where
  toFun b := ⟨T.π b.1, by
    rw [MonoidHom.mem_ker, T.derive_π, MonoidHom.mem_ker.mp b.2, map_one]⟩
  map_one' := Subtype.ext (map_one T.π)
  map_mul' a b := Subtype.ext (map_mul T.π a.1 b.1)

@[scoped simp] theorem πKer_coe (b : T.Q.derive.ker) : (T.πKer b : C) = T.π b.1 := rfl

noncomputable def inducedι : T.P.Tate0 →* T.Q.Tate0 :=
  QuotientGroup.map _ _ T.ιKer (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    obtain ⟨a, ha⟩ := hx
    exact ⟨T.ι a, by rw [T.norm_ι, ha]; rfl⟩)

noncomputable def inducedπ : T.Q.Tate0 →* T.R.Tate0 :=
  QuotientGroup.map _ _ T.πKer (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    obtain ⟨b, hb⟩ := hx
    exact ⟨T.π b, by rw [T.norm_π, hb]; rfl⟩)

@[scoped simp] theorem inducedι_mk (a : T.P.derive.ker) :
    T.inducedι (QuotientGroup.mk a) = QuotientGroup.mk (T.ιKer a) :=
  rfl

@[scoped simp] theorem inducedπ_mk (b : T.Q.derive.ker) :
    T.inducedπ (QuotientGroup.mk b) = QuotientGroup.mk (T.πKer b) :=
  rfl

def ConnectingRel (c : C) (a : A) : Prop :=
  ∃ b : B, T.π b = c ∧ T.ι a = T.Q.derive b

theorem connectingRel_exists {c : C} (hc : c ∈ T.R.derive.ker) :
    ∃ a, a ∈ T.P.norm.ker ∧ T.ConnectingRel c a := by
  obtain ⟨b, rfl⟩ := T.π_surjective c
  have hdb : T.π (T.Q.derive b) = 1 := by
    rw [← T.derive_π]
    exact MonoidHom.mem_ker.mp hc
  obtain ⟨a, ha⟩ := T.exists_of_π_eq_one hdb
  refine ⟨a, ?_, b, rfl, ha⟩
  rw [MonoidHom.mem_ker]
  apply T.ι_injective
  rw [← T.norm_ι, ha, T.Q.norm_derive, map_one]

theorem connectingRel_div_mem {c : C} {a a' : A} (h : T.ConnectingRel c a)
    (h' : T.ConnectingRel c a') : a / a' ∈ T.P.derive.range := by
  obtain ⟨b, hb, hab⟩ := h
  obtain ⟨b', hb', hab'⟩ := h'
  have hbb' : T.π (b / b') = 1 := by rw [map_div, hb, hb', div_self']
  obtain ⟨x, hx⟩ := T.exists_of_π_eq_one hbb'
  refine ⟨x, T.ι_injective ?_⟩
  rw [← T.derive_ι, hx, map_div, map_div, hab, hab']

theorem connectingRel_mul {c c' : C} {a a' : A} (h : T.ConnectingRel c a)
    (h' : T.ConnectingRel c' a') : T.ConnectingRel (c * c') (a * a') := by
  obtain ⟨b, hb, hab⟩ := h
  obtain ⟨b', hb', hab'⟩ := h'
  exact ⟨b * b', by rw [map_mul, hb, hb'], by rw [map_mul, map_mul, hab, hab']⟩

theorem connectingRel_one_of_mem_range_norm {c : C} (hc : c ∈ T.R.norm.range) :
    T.ConnectingRel c 1 := by
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨b', rfl⟩ := T.π_surjective c'
  exact ⟨T.Q.norm b', by rw [T.norm_π], by rw [map_one, T.Q.derive_norm]⟩

theorem connectingRel_one : T.ConnectingRel 1 1 :=
  ⟨1, map_one _, by rw [map_one, map_one]⟩

noncomputable def connectingAux (c : T.R.derive.ker) : A :=
  (T.connectingRel_exists c.2).choose

theorem connectingAux_mem (c : T.R.derive.ker) :
    T.connectingAux c ∈ T.P.norm.ker :=
  (T.connectingRel_exists c.2).choose_spec.1

theorem connectingAux_rel (c : T.R.derive.ker) :
    T.ConnectingRel c.1 (T.connectingAux c) :=
  (T.connectingRel_exists c.2).choose_spec.2

noncomputable def connectingHom : T.R.derive.ker →* T.P.Tate1 where
  toFun c := QuotientGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩
  map_one' := by
    rw [show (1 : T.P.Tate1) = QuotientGroup.mk ⟨1, T.P.norm.ker.one_mem⟩ from rfl]
    rw [tateQuot_mk_eq_mk]
    exact T.connectingRel_div_mem (T.connectingAux_rel 1) T.connectingRel_one
  map_mul' c c' := by
    rw [show (QuotientGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩ *
        QuotientGroup.mk ⟨T.connectingAux c', T.connectingAux_mem c'⟩ : T.P.Tate1) =
      QuotientGroup.mk ⟨T.connectingAux c * T.connectingAux c',
        T.P.norm.ker.mul_mem (T.connectingAux_mem c) (T.connectingAux_mem c')⟩ from rfl]
    rw [tateQuot_mk_eq_mk]
    exact T.connectingRel_div_mem (T.connectingAux_rel (c * c'))
      (T.connectingRel_mul (T.connectingAux_rel c) (T.connectingAux_rel c'))

noncomputable def connecting : T.R.Tate0 →* T.P.Tate1 :=
  QuotientGroup.lift _ T.connectingHom (by
    intro c hc
    rw [Subgroup.mem_subgroupOf] at hc
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩ : T.P.Tate1) = 1
    rw [show (1 : T.P.Tate1) = QuotientGroup.mk ⟨1, T.P.norm.ker.one_mem⟩ from rfl]
    rw [tateQuot_mk_eq_mk]
    exact T.connectingRel_div_mem (T.connectingAux_rel c)
      (T.connectingRel_one_of_mem_range_norm hc))

@[scoped simp] theorem connecting_mk (c : T.R.derive.ker) :
    T.connecting (QuotientGroup.mk c) =
      QuotientGroup.mk ⟨T.connectingAux c, T.connectingAux_mem c⟩ :=
  rfl

theorem connecting_mk_eq_of_rel {c : T.R.derive.ker} {a : A} (ha : a ∈ T.P.norm.ker)
    (hrel : T.ConnectingRel c.1 a) :
    T.connecting (QuotientGroup.mk c) = QuotientGroup.mk ⟨a, ha⟩ := by
  rw [connecting_mk, tateQuot_mk_eq_mk]
  exact T.connectingRel_div_mem (T.connectingAux_rel c) hrel

theorem exact_at_middle : T.inducedι.range = T.inducedπ.ker := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    refine QuotientGroup.induction_on y fun a => ?_
    rw [MonoidHom.mem_ker, inducedι_mk, inducedπ_mk, tateQuot_mk_eq_one]
    show T.π (T.ι a.1) ∈ T.R.norm.range
    rw [T.π_ι]
    exact one_mem _
  · intro x hx
    revert hx
    refine QuotientGroup.induction_on x fun b => ?_
    intro hb
    rw [MonoidHom.mem_ker, inducedπ_mk, tateQuot_mk_eq_one] at hb
    obtain ⟨c, hc⟩ := hb
    obtain ⟨b', rfl⟩ := T.π_surjective c
    have hsub : T.π (b.1 / T.Q.norm b') = 1 := by
      rw [map_div, ← T.norm_π, hc]
      show T.π b.1 / (T.πKer b).1 = 1
      rw [πKer_coe, div_self']
    obtain ⟨a, ha⟩ := T.exists_of_π_eq_one hsub
    have haker : a ∈ T.P.derive.ker := by
      rw [MonoidHom.mem_ker]
      apply T.ι_injective
      rw [← T.derive_ι, ha, map_one, map_div, T.Q.derive_norm,
        MonoidHom.mem_ker.mp b.2, div_one]
    refine ⟨QuotientGroup.mk ⟨a, haker⟩, ?_⟩
    rw [inducedι_mk, tateQuot_mk_eq_mk]
    show T.ι a / b.1 ∈ T.Q.norm.range
    rw [ha]
    refine ⟨b'⁻¹, ?_⟩
    rw [map_inv, eq_comm, div_right_comm, div_self', one_div]

theorem exact_at_quot : T.inducedπ.range = T.connecting.ker := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    refine QuotientGroup.induction_on y fun b => ?_
    rw [MonoidHom.mem_ker, inducedπ_mk]
    have hrel : T.ConnectingRel (T.πKer b).1 1 :=
      ⟨b.1, rfl, by rw [map_one, MonoidHom.mem_ker.mp b.2]⟩
    rw [T.connecting_mk_eq_of_rel T.P.norm.ker.one_mem hrel]
    exact (tateQuot_mk_eq_one _).mpr (one_mem _)
  · intro x hx
    revert hx
    refine QuotientGroup.induction_on x fun c => ?_
    intro hc
    rw [MonoidHom.mem_ker, connecting_mk, tateQuot_mk_eq_one] at hc
    obtain ⟨x', hx'⟩ := hc
    replace hx' : T.P.derive x' = T.connectingAux c := hx'
    obtain ⟨b, hb, hab⟩ := T.connectingAux_rel c
    have hbker : b / T.ι x' ∈ T.Q.derive.ker := by
      rw [MonoidHom.mem_ker, map_div, ← hab, T.derive_ι, hx', div_self']
    refine ⟨QuotientGroup.mk ⟨b / T.ι x', hbker⟩, ?_⟩
    rw [inducedπ_mk, tateQuot_mk_eq_mk]
    show T.π (b / T.ι x') / c.1 ∈ T.R.norm.range
    rw [map_div, T.π_ι, div_one, hb, div_self']
    exact one_mem _

theorem exact_at_sub : T.connecting.range = T.swap.inducedι.ker := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    refine QuotientGroup.induction_on y fun c => ?_
    obtain ⟨b, hb, hab⟩ := T.connectingAux_rel c
    show T.swap.inducedι (T.connecting (QuotientGroup.mk c)) = 1
    rw [connecting_mk]
    show (QuotientGroup.mk (T.swap.ιKer ⟨T.connectingAux c, T.connectingAux_mem c⟩) :
      T.swap.Q.Tate0) = 1
    rw [tateQuot_mk_eq_one]
    show T.ι (T.connectingAux c) ∈ T.Q.derive.range
    exact ⟨b, hab.symm⟩
  · intro x hx
    revert hx
    refine QuotientGroup.induction_on x fun a => ?_
    intro ha
    have ha' : T.ι a.1 ∈ T.Q.derive.range := by
      have h1 : (QuotientGroup.mk (T.swap.ιKer a) : T.swap.Q.Tate0) = 1 := ha
      rw [tateQuot_mk_eq_one] at h1
      exact h1
    obtain ⟨b, hb⟩ := ha'
    have hπb : T.π b ∈ T.R.derive.ker := by
      rw [MonoidHom.mem_ker, T.derive_π, hb]
      show T.π (T.ι a.1) = 1
      exact T.π_ι a.1
    refine ⟨QuotientGroup.mk ⟨T.π b, hπb⟩, ?_⟩
    exact T.connecting_mk_eq_of_rel a.2 ⟨b, rfl, hb.symm⟩

theorem tateCard_mul :
    T.P.tateCard₀ * T.R.tateCard₀ * T.Q.tateCard₁ =
      T.Q.tateCard₀ * T.P.tateCard₁ * T.R.tateCard₁ :=
  card_mul_eq_of_exactCycle
    T.inducedι T.inducedπ T.connecting T.swap.inducedι T.swap.inducedπ T.swap.connecting
    T.exact_at_middle T.exact_at_quot T.exact_at_sub
    T.swap.exact_at_middle T.swap.exact_at_quot T.swap.exact_at_sub

theorem finite_tate1_of (hR : T.R.tateCard₁ = 1) (hP : Finite T.P.Tate1) :
    Finite T.Q.Tate1 := by
  have hsub : Subsingleton T.R.Tate1 := (Nat.card_eq_one_iff_unique.mp hR).1
  haveI : Finite T.swap.P.Tate0 := hP
  have hsurj : Function.Surjective T.swap.inducedι := by
    intro y
    have hy : y ∈ T.swap.inducedπ.ker := by
      rw [MonoidHom.mem_ker]
      exact @Subsingleton.elim _ hsub _ _
    rw [← T.swap.exact_at_middle] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, hx⟩
  exact Finite.of_surjective _ hsurj

end MTriple
p2m_reactivate "P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction.MTriple"

def trivPair (C : Type*) [CommGroup C] (n : ℕ) : MPair C where
  derive := 1
  norm := powMonoidHom n
  derive_norm _ := rfl
  norm_derive _ := by simp

theorem tateCard₁_trivPair_int {n : ℕ} (hn : n ≠ 0) :
    (trivPair (Multiplicative ℤ) n).tateCard₁ = 1 := by
  rw [MPair.tateCard₁, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
  induction x using QuotientGroup.induction_on with
  | H x =>
  induction y using QuotientGroup.induction_on with
  | H y =>
  have hx : x = 1 := by
    apply Subtype.ext
    have h := MonoidHom.mem_ker.mp x.2
    change x.1 ^ n = 1 at h
    apply Multiplicative.toAdd.injective
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, mul_eq_zero] at h'
    rcases h' with h' | h'
    · exact absurd (by exact_mod_cast h') hn
    · simpa using h'
  have hy : y = 1 := by
    apply Subtype.ext
    have h := MonoidHom.mem_ker.mp y.2
    change y.1 ^ n = 1 at h
    apply Multiplicative.toAdd.injective
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, mul_eq_zero] at h'
    rcases h' with h' | h'
    · exact absurd (by exact_mod_cast h') hn
    · simpa using h'
  rw [hx, hy]

noncomputable def reduceModN (n : ℕ) :
    (trivPair (Multiplicative ℤ) n).derive.ker →* Multiplicative (ZMod n) where
  toFun x := Multiplicative.ofAdd (((Multiplicative.toAdd x.1 : ℤ)) : ZMod n)
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, ← Int.cast_add, ← toAdd_mul]
    rfl

theorem reduceModN_surjective (n : ℕ) : Function.Surjective (reduceModN n) := by
  intro y
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (Multiplicative.toAdd y)
  refine ⟨⟨Multiplicative.ofAdd z, MonoidHom.mem_ker.mpr rfl⟩, ?_⟩
  show Multiplicative.ofAdd (((Multiplicative.toAdd (Multiplicative.ofAdd z) : ℤ)) : ZMod n) = y
  rw [toAdd_ofAdd, hz, ofAdd_toAdd]

theorem reduceModN_ker (n : ℕ) :
    (reduceModN n).ker =
      (trivPair (Multiplicative ℤ) n).norm.range.subgroupOf
        (trivPair (Multiplicative ℤ) n).derive.ker := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h' : (((Multiplicative.toAdd x.1 : ℤ)) : ZMod n) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa [reduceModN] using this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    obtain ⟨k, hk⟩ := h'
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    show (Multiplicative.ofAdd k) ^ n = x.1
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, hk, nsmul_eq_mul]
  · rintro ⟨y, hy⟩
    change y ^ n = x.1 at hy
    show Multiplicative.ofAdd (((Multiplicative.toAdd x.1 : ℤ)) : ZMod n) = 1
    rw [← hy, toAdd_pow, nsmul_eq_mul]
    push_cast
    rw [ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem tateCard₀_trivPair_int (n : ℕ) :
    (trivPair (Multiplicative ℤ) n).tateCard₀ = n := by
  rw [MPair.tateCard₀, MPair.Tate0, ← reduceModN_ker]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (reduceModN_surjective n)).toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

section Concrete

open ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L)

attribute [local instance] Fintype.ofFinite

theorem coe_unitsAct (s : A.decompositionSubgroup K) (u : Aˣ) :
    ((unitsAct A s u : Aˣ) : A) = s • (u : A) := rfl

theorem coe_fieldUnitsAct (s : A.decompositionSubgroup K) (x : Lˣ) :
    ((fieldUnitsAct A s x : Lˣ) : L) = (s : L ≃ₐ[K] L) x := rfl

theorem coe_decomp_smul (s : A.decompositionSubgroup K) (a : A) :
    ((s • a : A) : L) = (s : L ≃ₐ[K] L) a := rfl

theorem unitsAct_mul_apply (s t : A.decompositionSubgroup K) (u : Aˣ) :
    unitsAct A (s * t) u = unitsAct A s (unitsAct A t u) :=
  Units.ext (mul_smul s t (u : A))

theorem fieldUnitsAct_mul_apply (s t : A.decompositionSubgroup K) (x : Lˣ) :
    fieldUnitsAct A (s * t) x = fieldUnitsAct A s (fieldUnitsAct A t x) :=
  Units.ext rfl

theorem unitsDerive_apply (g : A.decompositionSubgroup K) (u : Aˣ) :
    unitsDerive A g u = unitsAct A g u / u := rfl

theorem fieldUnitsDerive_apply (g : A.decompositionSubgroup K) (x : Lˣ) :
    fieldUnitsDerive A g x = fieldUnitsAct A g x / x := rfl

def unitsIncl : Aˣ →* Lˣ := Units.map (A.subtype : A →+* L).toMonoidHom

theorem coe_unitsIncl (u : Aˣ) : ((unitsIncl A u : Lˣ) : L) = ((u : A) : L) := rfl

theorem unitsIncl_injective : Function.Injective (unitsIncl A) :=
  Units.map_injective Subtype.coe_injective

theorem fieldUnitsAct_unitsIncl (s : A.decompositionSubgroup K) (u : Aˣ) :
    fieldUnitsAct A s (unitsIncl A u) = unitsIncl A (unitsAct A s u) :=
  Units.ext rfl

section FiniteGroup

variable [Finite (A.decompositionSubgroup K)]

theorem unitsNorm_apply (u : Aˣ) :
    unitsNorm (K := K) A u = ∏ s : A.decompositionSubgroup K, unitsAct A s u := by
  unfold unitsNorm
  exact MonoidHom.finsetProd_apply _ _ _

theorem fieldUnitsNorm_apply (x : Lˣ) :
    fieldUnitsNorm (K := K) A x = ∏ s : A.decompositionSubgroup K, fieldUnitsAct A s x := by
  unfold fieldUnitsNorm
  exact MonoidHom.finsetProd_apply _ _ _

theorem unitsNorm_unitsAct (t : A.decompositionSubgroup K) (u : Aˣ) :
    unitsNorm (K := K) A (unitsAct A t u) = unitsNorm (K := K) A u := by
  rw [unitsNorm_apply, unitsNorm_apply]
  exact Fintype.prod_equiv (Equiv.mulRight t) _ _
    (fun s => by rw [Equiv.coe_mulRight, unitsAct_mul_apply])

theorem unitsAct_unitsNorm (t : A.decompositionSubgroup K) (u : Aˣ) :
    unitsAct A t (unitsNorm (K := K) A u) = unitsNorm (K := K) A u := by
  rw [unitsNorm_apply, map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft t) _ _
    (fun s => by rw [Equiv.coe_mulLeft, unitsAct_mul_apply])

theorem fieldUnitsNorm_fieldUnitsAct (t : A.decompositionSubgroup K) (x : Lˣ) :
    fieldUnitsNorm (K := K) A (fieldUnitsAct A t x) = fieldUnitsNorm (K := K) A x := by
  rw [fieldUnitsNorm_apply, fieldUnitsNorm_apply]
  exact Fintype.prod_equiv (Equiv.mulRight t) _ _
    (fun s => by rw [Equiv.coe_mulRight, fieldUnitsAct_mul_apply])

theorem fieldUnitsAct_fieldUnitsNorm (t : A.decompositionSubgroup K) (x : Lˣ) :
    fieldUnitsAct A t (fieldUnitsNorm (K := K) A x) = fieldUnitsNorm (K := K) A x := by
  rw [fieldUnitsNorm_apply, map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft t) _ _
    (fun s => by rw [Equiv.coe_mulLeft, fieldUnitsAct_mul_apply])

theorem fieldUnitsNorm_unitsIncl (u : Aˣ) :
    fieldUnitsNorm (K := K) A (unitsIncl A u) = unitsIncl A (unitsNorm (K := K) A u) := by
  rw [fieldUnitsNorm_apply, unitsNorm_apply, map_prod]
  exact Finset.prod_congr rfl (fun s _ => fieldUnitsAct_unitsIncl A s u)

variable (K) in

noncomputable def unitsPair (g : A.decompositionSubgroup K) : MPair Aˣ where
  derive := unitsDerive A g
  norm := unitsNorm (K := K) A
  derive_norm u := by
    rw [unitsDerive_apply, unitsAct_unitsNorm, div_self']
  norm_derive u := by
    rw [unitsDerive_apply, map_div, unitsNorm_unitsAct, div_self']

variable (K) in

noncomputable def fieldPair (g : A.decompositionSubgroup K) : MPair Lˣ where
  derive := fieldUnitsDerive A g
  norm := fieldUnitsNorm (K := K) A
  derive_norm x := by
    rw [fieldUnitsDerive_apply, fieldUnitsAct_fieldUnitsNorm, div_self']
  norm_derive x := by
    rw [fieldUnitsDerive_apply, map_div, fieldUnitsNorm_fieldUnitsAct, div_self']

end FiniteGroup
p2m_reactivate "P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction.MTriple"

section DVR

variable [IsDiscreteValuationRing A]

theorem exists_unit_smul_eq (s : A.decompositionSubgroup K) (y : A) (hy : y ≠ 0) :
    ∃ w : Aˣ, s • y = w * y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  have hsϖ : Irreducible (s • ϖ) :=
    (MulEquiv.irreducible_iff
      (MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A s)).mpr hϖ
  obtain ⟨w₀, hw₀⟩ := IsDiscreteValuationRing.associated_of_irreducible A hϖ hsϖ
  refine ⟨unitsAct A s u * w₀ ^ k * u⁻¹, ?_⟩
  have hu : ((u⁻¹ : Aˣ) : A) * u = 1 := u.inv_mul
  rw [smul_mul', smul_pow', ← hw₀, mul_pow, Units.val_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, coe_unitsAct]
  linear_combination (-(s • (u : A)) * (w₀ : A) ^ k * ϖ ^ k) * hu

theorem fieldUnitsAct_div_mem_of_mem (s : A.decompositionSubgroup K) (x : Lˣ)
    (hx : (x : L) ∈ A) : fieldUnitsAct A s x / x ∈ (unitsIncl A).range := by
  have hy : (⟨x, hx⟩ : A) ≠ 0 := fun e => x.ne_zero (congrArg Subtype.val e)
  obtain ⟨w, hw⟩ := exists_unit_smul_eq A s ⟨x, hx⟩ hy
  have hw' : (s : L ≃ₐ[K] L) x = ((w : A) : L) * x := congrArg Subtype.val hw
  refine ⟨w, Units.ext ?_⟩
  rw [coe_unitsIncl, Units.val_div_eq_div_val, coe_fieldUnitsAct, hw',
    mul_div_cancel_right₀ _ x.ne_zero]

theorem fieldUnitsAct_div_mem (s : A.decompositionSubgroup K) (x : Lˣ) :
    fieldUnitsAct A s x / x ∈ (unitsIncl A).range := by
  rcases A.mem_or_inv_mem (x : L) with h | h
  · exact fieldUnitsAct_div_mem_of_mem A s x h
  · rw [← Units.val_inv_eq_inv_val] at h
    have := fieldUnitsAct_div_mem_of_mem A s x⁻¹ h
    rw [map_inv, inv_div_inv] at this
    rw [← Subgroup.inv_mem_iff, inv_div]
    exact this

noncomputable def unif : A := (IsDiscreteValuationRing.exists_irreducible A).choose

theorem unif_irreducible : Irreducible (unif A) :=
  (IsDiscreteValuationRing.exists_irreducible A).choose_spec

theorem unif_coe_ne_zero : ((unif A : A) : L) ≠ 0 := fun h =>
  (unif_irreducible A).ne_zero (Subtype.coe_injective (by simpa using h))

noncomputable def unifUnit : Lˣ := Units.mk0 _ (unif_coe_ne_zero A)

theorem coe_unifUnit : ((unifUnit A : Lˣ) : L) = ((unif A : A) : L) := rfl

theorem eq_incl_mul_zpow_of_mem (x : Lˣ) (hx : (x : L) ∈ A) :
    ∃ (n : ℕ) (u : Aˣ), x = unitsIncl A u * unifUnit A ^ (n : ℤ) := by
  have hy : (⟨x, hx⟩ : A) ≠ 0 := fun e => x.ne_zero (congrArg Subtype.val e)
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy (unif_irreducible A)
  refine ⟨n, u, Units.ext ?_⟩
  have := congrArg Subtype.val hu
  push_cast at this
  rw [zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, coe_unitsIncl, coe_unifUnit]
  exact this

theorem eq_incl_mul_zpow (x : Lˣ) :
    ∃ (k : ℤ) (u : Aˣ), x = unitsIncl A u * unifUnit A ^ k := by
  rcases A.mem_or_inv_mem (x : L) with h | h
  · obtain ⟨n, u, e⟩ := eq_incl_mul_zpow_of_mem A x h
    exact ⟨n, u, e⟩
  · rw [← Units.val_inv_eq_inv_val] at h
    obtain ⟨n, u, e⟩ := eq_incl_mul_zpow_of_mem A x⁻¹ h
    refine ⟨-(n : ℤ), u⁻¹, ?_⟩
    rw [← inv_inv x, e, mul_inv, ← map_inv, zpow_neg]

theorem eq_zero_of_incl_eq_zpow_nat (n : ℕ) (u : Aˣ)
    (hu : unitsIncl A u = unifUnit A ^ (n : ℤ)) : n = 0 := by
  by_contra hn
  have h1 : ((u : A) : L) = ((unif A ^ n : A) : L) := by
    have := congrArg (fun v : Lˣ => (v : L)) hu
    simp only [coe_unitsIncl, zpow_natCast, Units.val_pow_eq_pow_val, coe_unifUnit] at this
    rw [this, SubmonoidClass.coe_pow]
  have h2 : (u : A) = unif A ^ n := Subtype.coe_injective h1
  have h3 : IsUnit (unif A ^ n) := h2 ▸ Units.isUnit u
  exact (unif_irreducible A).not_isUnit ((isUnit_pow_iff hn).mp h3)

theorem eq_zero_of_zpow_mem (k : ℤ) (hk : unifUnit A ^ k ∈ (unitsIncl A).range) : k = 0 := by
  obtain ⟨u, hu⟩ := hk
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact_mod_cast eq_zero_of_incl_eq_zpow_nat A n u hu
  · have hu' : unitsIncl A u⁻¹ = unifUnit A ^ (n : ℤ) := by
      rw [map_inv, hu, zpow_neg, inv_inv]
    have := eq_zero_of_incl_eq_zpow_nat A n u⁻¹ hu'
    subst this
    simp

noncomputable def zpowQuot : Multiplicative ℤ →* Lˣ ⧸ (unitsIncl A).range where
  toFun k := QuotientGroup.mk (unifUnit A ^ (Multiplicative.toAdd k))
  map_one' := by rw [toAdd_one, zpow_zero]; rfl
  map_mul' a b := by rw [toAdd_mul, zpow_add]; rfl

theorem zpowQuot_apply (k : Multiplicative ℤ) :
    zpowQuot A k = QuotientGroup.mk (unifUnit A ^ (Multiplicative.toAdd k)) := rfl

theorem zpowQuot_bijective : Function.Bijective (zpowQuot A) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro k hk
    rw [MonoidHom.mem_ker, zpowQuot_apply, QuotientGroup.eq_one_iff] at hk
    have := eq_zero_of_zpow_mem A _ hk
    exact Multiplicative.toAdd.injective this
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
    obtain ⟨k, u, rfl⟩ := eq_incl_mul_zpow A x
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    rw [zpowQuot_apply, toAdd_ofAdd]
    apply QuotientGroup.eq.mpr
    rw [mul_comm (unitsIncl A u), ← mul_assoc, inv_mul_cancel, one_mul]
    exact ⟨u, rfl⟩

noncomputable def ordHom : Lˣ →* Multiplicative ℤ :=
  (MulEquiv.ofBijective (zpowQuot A) (zpowQuot_bijective A)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (unitsIncl A).range)

theorem ordHom_surjective : Function.Surjective (ordHom A) := by
  intro k
  obtain ⟨q, hq⟩ :=
    (MulEquiv.ofBijective (zpowQuot A) (zpowQuot_bijective A)).symm.surjective k
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, hq⟩

theorem ordHom_ker : (ordHom A).ker = (unitsIncl A).range := by
  ext x
  rw [MonoidHom.mem_ker, ordHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem ordHom_eq_of_div_mem {x y : Lˣ} (h : x / y ∈ (unitsIncl A).range) :
    ordHom A x = ordHom A y := by
  rw [← ordHom_ker, MonoidHom.mem_ker, map_div, div_eq_one] at h
  exact h

theorem ordHom_fieldUnitsAct (s : A.decompositionSubgroup K) (x : Lˣ) :
    ordHom A (fieldUnitsAct A s x) = ordHom A x :=
  ordHom_eq_of_div_mem A (fieldUnitsAct_div_mem A s x)

variable [Finite (A.decompositionSubgroup K)]

variable (K) in

noncomputable def valuationTriple (g : A.decompositionSubgroup K) :
    MTriple Aˣ Lˣ (Multiplicative ℤ) where
  P := unitsPair K A g
  Q := fieldPair K A g
  R := trivPair (Multiplicative ℤ) (Nat.card (A.decompositionSubgroup K))
  ι := unitsIncl A
  π := ordHom A
  ι_injective := unitsIncl_injective A
  π_surjective := ordHom_surjective A
  exact := (ordHom_ker A).symm
  derive_ι u := by
    show fieldUnitsDerive A g (unitsIncl A u) = unitsIncl A (unitsDerive A g u)
    rw [fieldUnitsDerive_apply, unitsDerive_apply, map_div, fieldUnitsAct_unitsIncl]
  norm_ι u := fieldUnitsNorm_unitsIncl A u
  derive_π x := by
    show (1 : Multiplicative ℤ →* Multiplicative ℤ) (ordHom A x) =
      ordHom A (fieldUnitsDerive A g x)
    rw [MonoidHom.one_apply, fieldUnitsDerive_apply, map_div, ordHom_fieldUnitsAct, div_self']
  norm_π x := by
    show powMonoidHom (Nat.card (A.decompositionSubgroup K)) (ordHom A x) =
      ordHom A (fieldUnitsNorm (K := K) A x)
    rw [powMonoidHom_apply, fieldUnitsNorm_apply, map_prod]
    simp_rw [ordHom_fieldUnitsAct]
    rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

variable (K) in

theorem fieldUnits_herbrand (g : A.decompositionSubgroup K)
    (hP : (unitsPair K A g).tateCard₀ = (unitsPair K A g).tateCard₁)
    (hPne : (unitsPair K A g).tateCard₀ ≠ 0) :
    (fieldPair K A g).tateCard₀ =
        Nat.card (A.decompositionSubgroup K) * (fieldPair K A g).tateCard₁ ∧
      (fieldPair K A g).tateCard₁ ≠ 0 := by
  have hn : Nat.card (A.decompositionSubgroup K) ≠ 0 := Nat.card_pos.ne'
  have hR₁ : (trivPair (Multiplicative ℤ) (Nat.card (A.decompositionSubgroup K))).tateCard₁
      = 1 := tateCard₁_trivPair_int hn
  have key : (unitsPair K A g).tateCard₀ *
      (trivPair (Multiplicative ℤ) (Nat.card (A.decompositionSubgroup K))).tateCard₀ *
        (fieldPair K A g).tateCard₁ =
      (fieldPair K A g).tateCard₀ * (unitsPair K A g).tateCard₁ *
        (trivPair (Multiplicative ℤ) (Nat.card (A.decompositionSubgroup K))).tateCard₁ :=
    (valuationTriple K A g).tateCard_mul
  rw [tateCard₀_trivPair_int, hR₁, mul_one, ← hP] at key
  have hfinP : Finite (unitsPair K A g).Tate1 := by
    apply Nat.finite_of_card_ne_zero
    show (unitsPair K A g).tateCard₁ ≠ 0
    rw [← hP]; exact hPne
  have hfinQ : Finite (fieldPair K A g).Tate1 :=
    (valuationTriple K A g).finite_tate1_of hR₁ hfinP
  refine ⟨?_, Nat.card_pos.ne'⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hPne)
  calc (unitsPair K A g).tateCard₀ * (fieldPair K A g).tateCard₀
      = (fieldPair K A g).tateCard₀ * (unitsPair K A g).tateCard₀ := mul_comm _ _
    _ = (unitsPair K A g).tateCard₀ * Nat.card (A.decompositionSubgroup K) *
          (fieldPair K A g).tateCard₁ := key.symm
    _ = _ := mul_assoc _ _ _

end DVR
p2m_reactivate "P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction.MTriple"

end Concrete
p2m_reactivate "P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction.MTriple"

end FieldUnitsHerbrandReduction
p2m_reactivate "P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction.MTriple P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction"
end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction.MTriple P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT.FieldUnitsHerbrandReduction P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT"

open _root_.M4aLocalCFT _root_.P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.M4aLocalCFT M4aLocalCFT.FieldUnitsHerbrandReduction in

theorem solution (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((fieldUnitsDerive A g).ker ⧸
      ((fieldUnitsNorm (K := K) A).range.subgroupOf (fieldUnitsDerive A g).ker)) =
    Nat.card (A.decompositionSubgroup K) *
    Nat.card ((fieldUnitsNorm (K := K) A).ker ⧸
      ((fieldUnitsDerive A g).range.subgroupOf (fieldUnitsNorm (K := K) A).ker)) ∧
    Nat.card ((fieldUnitsNorm (K := K) A).ker ⧸
      ((fieldUnitsDerive A g).range.subgroupOf (fieldUnitsNorm (K := K) A).ker)) ≠ 0 := by
  obtain ⟨hP, hPne⟩ := M4aLocalCFT.unitsDecomp_herbrandQuotient_eq_one K A g hg
  exact fieldUnits_herbrand K A g hP hPne

end S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card
end P2MW
export P2MW.S_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card (solution)
