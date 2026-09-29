-- Prove2me | solution 1 for Ihara.commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ab64a14b-89c3-56fe-9ea4-896d36fd2cb2

import Definitions.Def_SchurMultiplierTrivial
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod

set_option Elab.async false

section Inl_A3_EllStem

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton"
p2m_open "Ihara"

open Subgroup

open scoped commutatorElement

universe u

section Central

variable {E : Type*} [Group E]

theorem commutatorElement_mul_left_of_mem_center {a b z : E} (hz : z ∈ center E) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz' := mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_assoc a z b, ← hz' b,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_mem_center {a b z : E} (hz : z ∈ center E) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_mem_center hz, commutatorElement_inv]

theorem commutator_eq_of_mul_center (X : Subgroup E)
    (hX : ∀ e : E, ∃ c ∈ X, ∃ z ∈ center E, e = c * z) : commutator E = ⁅X, X⁆ := by
  refine le_antisymm ?_ (commutator_mono le_top le_top)
  rw [commutator_def, commutator_le]
  rintro a - b -
  obtain ⟨c, hc, z, hz, rfl⟩ := hX a
  obtain ⟨d, hd, w, hw, rfl⟩ := hX b
  rw [commutatorElement_mul_left_of_mem_center hz, commutatorElement_mul_right_of_mem_center hw]
  exact commutator_mem_commutator hc hd

end Central

section PerfectStem

variable {F E : Type u} [Group F] [Group E]

theorem eq_one_of_perfect_of_hasTrivialSchurMultiplier (hperf : commutator F = ⊤)
    (hstem : HasTrivialSchurMultiplier F) (π : E →* F) (hsurj : Function.Surjective π)
    (hcent : π.ker ≤ center E) {x : E} (hx : x ∈ π.ker) (hxc : x ∈ commutator E) : x = 1 := by
  set X : Subgroup E := commutator E with hXdef

  have hXmap : X.map π = ⊤ := by
    rw [hXdef, map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj, ← commutator_def, hperf]

  have hdec : ∀ e : E, ∃ c ∈ X, ∃ z ∈ center E, e = c * z := by
    intro e
    have he : π e ∈ X.map π := by rw [hXmap]; exact mem_top _
    obtain ⟨c, hc, hce⟩ := he
    refine ⟨c, hc, c⁻¹ * e, hcent ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]

  have hXX : ⁅X, X⁆ = X := (commutator_eq_of_mul_center X hdec).symm

  set π' : X →* F := π.comp X.subtype with hπ'
  have hsurj' : Function.Surjective π' := by
    intro f
    have hf : f ∈ X.map π := by rw [hXmap]; exact mem_top _
    obtain ⟨c, hc, rfl⟩ := hf
    exact ⟨⟨c, hc⟩, rfl⟩
  have hcent' : π'.ker ≤ center X := by
    intro y hy
    rw [mem_center_iff]
    intro g
    have hyc : (y : E) ∈ center E := hcent (by simpa [hπ'] using hy)
    exact Subtype.ext ((mem_center_iff.mp hyc) g)
  have hcomm' : π'.ker ≤ commutator X := by
    intro y _
    have hy : (y : E) ∈ ⁅X, X⁆ := by rw [hXX]; exact y.2
    rw [← map_subtype_commutator] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    rwa [← Subtype.coe_injective hyy]
  have hker : π'.ker = ⊥ := hstem X π' hsurj' hcent' hcomm'

  have hx' : (⟨x, hxc⟩ : X) ∈ π'.ker := by simpa [hπ'] using hx
  rw [hker, mem_bot] at hx'
  exact congrArg Subtype.val hx'

end PerfectStem

section Product

variable {F₁ F₂ E : Type u} [Group F₁] [Group F₂] [Group E]

def fstPreimage (π : E →* F₁ × F₂) : Subgroup E := ((MonoidHom.snd F₁ F₂).comp π).ker

def sndPreimage (π : E →* F₁ × F₂) : Subgroup E := ((MonoidHom.fst F₁ F₂).comp π).ker

theorem mem_fstPreimage {π : E →* F₁ × F₂} {e : E} : e ∈ fstPreimage π ↔ (π e).2 = 1 := Iff.rfl

theorem mem_sndPreimage {π : E →* F₁ × F₂} {e : E} : e ∈ sndPreimage π ↔ (π e).1 = 1 := Iff.rfl

variable (π : E →* F₁ × F₂) (hsurj : Function.Surjective π) (hcent : π.ker ≤ center E)

include hsurj in
theorem map_fstPreimage : (fstPreimage π).map π = (⊤ : Subgroup F₁).prod ⊥ := by
  ext ⟨f₁, f₂⟩
  simp only [mem_map, mem_fstPreimage, mem_prod, mem_top, mem_bot, true_and]
  constructor
  · rintro ⟨e, he, hef⟩
    rw [hef] at he
    exact he
  · rintro rfl
    obtain ⟨e, he⟩ := hsurj (f₁, 1)
    exact ⟨e, by rw [he], he⟩

include hsurj in
theorem map_sndPreimage : (sndPreimage π).map π = (⊥ : Subgroup F₁).prod ⊤ := by
  ext ⟨f₁, f₂⟩
  simp only [mem_map, mem_sndPreimage, mem_prod, mem_top, mem_bot, and_true]
  constructor
  · rintro ⟨e, he, hef⟩
    rw [hef] at he
    exact he
  · rintro rfl
    obtain ⟨e, he⟩ := hsurj (1, f₂)
    exact ⟨e, by rw [he], he⟩

include hcent in

theorem commutator_fst_snd_le_center : ⁅fstPreimage π, sndPreimage π⁆ ≤ center E := by
  refine le_trans ?_ hcent
  rw [commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
  rw [mem_fstPreimage] at ha
  rw [mem_sndPreimage] at hb
  ext
  · simp [hb]
  · simp [ha]

include hsurj hcent in

theorem commutator_fst_snd_eq_bot (hperf : commutator F₁ = ⊤) :
    ⁅fstPreimage π, sndPreimage π⁆ = ⊥ := by
  set H₁ := fstPreimage π
  set H₂ := sndPreimage π
  have hc : ⁅H₁, H₂⁆ ≤ center E := commutator_fst_snd_le_center π hcent

  have h3 : ⁅⁅H₁, H₁⁆, H₂⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [commutator_eq_bot_iff_le_centralizer]
      exact le_trans hc (center_le_centralizer _)
    · rw [commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact le_trans hc (center_le_centralizer _)

  have hmap : (⁅H₁, H₁⁆ : Subgroup E).map π = (⊤ : Subgroup F₁).prod ⊥ := by
    rw [map_commutator, map_fstPreimage π hsurj, commutator_prod_prod, ← commutator_def, hperf,
      commutator_bot_left]
  rw [eq_bot_iff, commutator_le]
  intro a ha b hb
  have ha' : π a ∈ (⁅H₁, H₁⁆ : Subgroup E).map π := by
    rw [hmap, mem_prod]; exact ⟨mem_top _, ha⟩
  obtain ⟨c, hc1, hca⟩ := ha'
  have hz : c⁻¹ * a ∈ center E := hcent (by rw [MonoidHom.mem_ker, map_mul, map_inv, hca,
    inv_mul_cancel])
  have : a = c * (c⁻¹ * a) := by group
  rw [this, commutatorElement_mul_left_of_mem_center hz, ← h3]
  exact commutator_mem_commutator hc1 hb

include hsurj hcent in
theorem commute_of_perfect_fst (hperf : commutator F₁ = ⊤) {a b : E} (ha : (π a).2 = 1)
    (hb : (π b).1 = 1) : Commute a b := by
  have h := commutator_fst_snd_eq_bot π hsurj hcent hperf
  rw [eq_bot_iff, commutator_le] at h
  exact (commutatorElement_eq_one_iff_commute).mp ((mem_bot).mp (h a ha b hb))

include hsurj hcent in

theorem pow_eq_one_of_prod (hperf : commutator F₁ = ⊤) (hstem : HasTrivialSchurMultiplier F₁)
    {n : ℕ}
    (hF₂ : ∀ (E' : Type u) [Group E'] (π' : E' →* F₂), Function.Surjective π' →
      π'.ker ≤ center E' → ∀ y ∈ π'.ker, y ∈ commutator E' → y ^ n = 1)
    {x : E} (hx : x ∈ π.ker) (hxc : x ∈ commutator E) : x ^ n = 1 := by
  set H₁ := fstPreimage π
  set H₂ := sndPreimage π

  have hcomm : ∀ (a : H₁) (b : H₂), Commute ((H₁.subtype) a) ((H₂.subtype) b) :=
    fun a b => commute_of_perfect_fst π hsurj hcent hperf a.2 b.2
  set μ : H₁ × H₂ →* E := MonoidHom.noncommCoprod H₁.subtype H₂.subtype hcomm with hμ
  have hμsurj : Function.Surjective μ := by
    intro e
    obtain ⟨a, ha⟩ := hsurj ((π e).1, 1)
    have ha1 : a ∈ H₁ := by rw [mem_fstPreimage, ha]
    have hb2 : a⁻¹ * e ∈ H₂ := by
      rw [mem_sndPreimage, map_mul, map_inv, ha, Prod.fst_mul, Prod.fst_inv, inv_mul_cancel]
    exact ⟨(⟨a, ha1⟩, ⟨a⁻¹ * e, hb2⟩), by simp [hμ]⟩

  have hxμ : x ∈ (commutator (H₁ × H₂)).map μ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hμsurj, ← commutator_def]; exact hxc
  rw [commutator_def, ← top_prod_top, commutator_prod_prod] at hxμ
  obtain ⟨⟨c₁, c₂⟩, ⟨hc₁, hc₂⟩, hcx⟩ := hxμ
  simp only [hμ, MonoidHom.noncommCoprod_apply, coe_subtype] at hcx

  have hπx : π x = 1 := hx
  have hπc₁2 : (π c₁).2 = 1 := c₁.2
  have hπc₂1 : (π c₂).1 = 1 := c₂.2
  have hπc₁ : π (c₁ : E) = 1 := by
    have h1 : (π c₁).1 * (π c₂).1 = 1 := by
      rw [← Prod.fst_mul, ← map_mul, hcx, hπx, Prod.fst_one]
    rw [hπc₂1, mul_one] at h1
    exact Prod.ext h1 hπc₁2
  have hπc₂ : π (c₂ : E) = 1 := by
    have h := congrArg π hcx
    rwa [map_mul, hπc₁, one_mul, hπx] at h

  set π₁ : H₁ →* F₁ := (MonoidHom.fst F₁ F₂).comp (π.comp H₁.subtype) with hπ₁
  have hsurj₁ : Function.Surjective π₁ := by
    intro f
    obtain ⟨a, ha⟩ := hsurj (f, 1)
    exact ⟨⟨a, by rw [mem_fstPreimage, ha]⟩, by simp [hπ₁, ha]⟩
  have hker₁ : ∀ y : H₁, y ∈ π₁.ker → (y : E) ∈ π.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    exact Prod.ext hy y.2
  have hcent₁ : π₁.ker ≤ center H₁ := by
    intro y hy
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_center_iff.mp (hcent (hker₁ y hy))) g)
  have hc₁one : c₁ = 1 :=
    eq_one_of_perfect_of_hasTrivialSchurMultiplier hperf hstem π₁ hsurj₁ hcent₁
      (by rw [MonoidHom.mem_ker]; simp [hπ₁, hπc₁]) (by rw [← commutator_def] at hc₁; exact hc₁)

  set π₂ : H₂ →* F₂ := (MonoidHom.snd F₁ F₂).comp (π.comp H₂.subtype) with hπ₂
  have hsurj₂ : Function.Surjective π₂ := by
    intro f
    obtain ⟨a, ha⟩ := hsurj (1, f)
    exact ⟨⟨a, by rw [mem_sndPreimage, ha]⟩, by simp [hπ₂, ha]⟩
  have hker₂ : ∀ y : H₂, y ∈ π₂.ker → (y : E) ∈ π.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    exact Prod.ext y.2 hy
  have hcent₂ : π₂.ker ≤ center H₂ := by
    intro y hy
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_center_iff.mp (hcent (hker₂ y hy))) g)
  have hc₂n : c₂ ^ n = 1 :=
    hF₂ H₂ π₂ hsurj₂ hcent₂ c₂ (by rw [MonoidHom.mem_ker]; simp [hπ₂, hπc₂])
      (by rw [← commutator_def] at hc₂; exact hc₂)

  rw [← hcx, hc₁one, OneMemClass.coe_one, one_mul, ← SubgroupClass.coe_pow, hc₂n,
    OneMemClass.coe_one]

include hsurj hcent in

theorem ker_eq_bot_of_prod_of_perfect (hperf₁ : commutator F₁ = ⊤)
    (hstem₁ : HasTrivialSchurMultiplier F₁) (hperf₂ : commutator F₂ = ⊤)
    (hstem₂ : HasTrivialSchurMultiplier F₂) (hcomm : π.ker ≤ commutator E) : π.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ^ 1 = 1 :=
    pow_eq_one_of_prod π hsurj hcent hperf₁ hstem₁ (n := 1)
      (fun E' _ π' hs hc y hy hyc => by
        rw [pow_one]
        exact eq_one_of_perfect_of_hasTrivialSchurMultiplier hperf₂ hstem₂ π' hs hc hy hyc)
      hx (hcomm hx)
  rwa [pow_one, ← mem_bot] at h1

end Product

theorem commutator_prod_eq_top {F₁ F₂ : Type*} [Group F₁] [Group F₂] (h₁ : commutator F₁ = ⊤)
    (h₂ : commutator F₂ = ⊤) : commutator (F₁ × F₂) = ⊤ := by
  rw [commutator_def, ← top_prod_top, commutator_prod_prod, ← commutator_def, ← commutator_def, h₁,
    h₂]

theorem hasTrivialSchurMultiplier_prod_of_perfect {F₁ F₂ : Type u} [Group F₁] [Group F₂]
    (hperf₁ : commutator F₁ = ⊤) (hstem₁ : HasTrivialSchurMultiplier F₁)
    (hperf₂ : commutator F₂ = ⊤) (hstem₂ : HasTrivialSchurMultiplier F₂) :
    HasTrivialSchurMultiplier (F₁ × F₂) := by
  intro E _ π hsurj hcent hcomm
  exact ker_eq_bot_of_prod_of_perfect π hsurj hcent hperf₁ hstem₁ hperf₂ hstem₂ hcomm

theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (h : commutator H = ⊤)
    (e : G ≃* H) : commutator G = ⊤ := by
  have := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rwa [map_commutator_eq, MonoidHom.range_eq_top.mpr e.symm.surjective, ← commutator_def,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.symm.surjective] at this

end Ihara

end Inl_A3_EllStem

section Inl_A3_SL2ZModFacts

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton"
p2m_open "Ihara"

open Matrix Polynomial

open scoped MatrixGroups

private theorem sl2coeZ_pow {R : Type*} [CommRing R] (A : SL(2, R)) (k : ℕ) :
    ((A ^ k : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = (A : Matrix (Fin 2) (Fin 2) R) ^ k :=
  rfl

private theorem sl2coeZ_one {R : Type*} [CommRing R] :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl

section CRT

variable (R S : Type*) [CommRing R] [CommRing S]

def slProdEquiv : SL(2, R × S) ≃* SL(2, R) × SL(2, S) where
  toFun := (SpecialLinearGroup.map (RingHom.fst R S)).prod (SpecialLinearGroup.map (RingHom.snd R S))
  invFun gh :=
    ⟨of fun i j => (((gh.1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) i j,
        ((gh.2 : SL(2, S)) : Matrix (Fin 2) (Fin 2) S) i j), by
      have h1 := gh.1.prop
      have h2 := gh.2.prop
      rw [det_fin_two] at h1 h2 ⊢
      exact Prod.ext (by simpa using h1) (by simpa using h2)⟩
  left_inv g := Subtype.ext <| Matrix.ext fun _ _ => rfl
  right_inv gh := Prod.ext (Subtype.ext <| Matrix.ext fun _ _ => rfl)
    (Subtype.ext <| Matrix.ext fun _ _ => rfl)
  map_mul' := map_mul _

variable {R S} in

def slCongr (e : R ≃+* S) : SL(2, R) ≃* SL(2, S) where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv _ := Subtype.ext <| Matrix.ext fun _ _ => e.symm_apply_apply _
  right_inv _ := Subtype.ext <| Matrix.ext fun _ _ => e.apply_symm_apply _
  map_mul' := map_mul _

noncomputable def slZModMulEquiv {a b : ℕ} (h : Nat.Coprime a b) :
    SL(2, ZMod (a * b)) ≃* SL(2, ZMod a) × SL(2, ZMod b) :=
  (slCongr (ZMod.chineseRemainder h)).trans (slProdEquiv (ZMod a) (ZMod b))

end CRT

section SmallPrimes

variable {R : Type*} [CommRing R]

theorem sq_eq_trace_smul_sub_one (A : SL(2, R)) :
    (A : Matrix (Fin 2) (Fin 2) R) * A = (Matrix.trace (A : Matrix (Fin 2) (Fin 2) R)) • (A : Matrix (Fin 2) (Fin 2) R) - 1 := by
  have hdet := A.prop
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first
    | ring1
    | linear_combination (-1 : R) * hdet

theorem pow_twelve_eq_one_of_sq_eq {A : Matrix (Fin 2) (Fin 2) R} {t : R}
    (ht : t = 0 ∨ t = 1 ∨ t = -1) (hA : A * A = t • A - 1) : A ^ 12 = 1 := by
  rcases ht with rfl | rfl | rfl
  · rw [zero_smul, zero_sub] at hA
    rw [show 12 = 2 * 6 from rfl, pow_mul, sq, hA]
    exact Even.neg_one_pow ⟨3, rfl⟩
  · rw [one_smul] at hA
    have h3 : A ^ 3 = -1 := by
      rw [pow_succ, sq, hA, sub_mul, one_mul, hA]; abel
    rw [show 12 = 3 * 4 from rfl, pow_mul, h3]
    exact Even.neg_one_pow ⟨2, rfl⟩
  · rw [neg_smul, one_smul] at hA
    have h3 : A ^ 3 = 1 := by
      rw [pow_succ, sq, hA, sub_mul, neg_mul, one_mul, hA]; abel
    rw [show 12 = 3 * 4 from rfl, pow_mul, h3, one_pow]

theorem pow_twelve_eq_one_SL2_ZMod {p : ℕ} (hp : p = 2 ∨ p = 3) (A : SL(2, ZMod p)) :
    A ^ 12 = 1 := by
  apply Subtype.ext
  rw [sl2coeZ_pow, sl2coeZ_one]
  refine pow_twelve_eq_one_of_sq_eq ?_ (sq_eq_trace_smul_sub_one A)
  generalize Matrix.trace (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = t
  rcases hp with rfl | rfl
  · revert t; decide
  · revert t; decide

theorem pow_eq_one_of_map_castHom_eq_one {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    (H : SL(2, ZMod (p ^ n)))
    (hH : SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self p hn) (ZMod p)) H = 1) :
    H ^ (p ^ (n - 1)) = 1 := by
  have hp : (p : ℕ).Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.add_sub_cancel]
  set 𝕄 := Matrix (Fin 2) (Fin 2) (ZMod (p ^ (k + 1)))

  have hentry : ∀ i j, ∃ c : ℕ, ((H : 𝕄) - 1) i j = (p : ZMod (p ^ (k + 1))) * c := by
    intro i j
    have hij := congrArg (fun M : SL(2, ZMod p) => (M : Matrix (Fin 2) (Fin 2) (ZMod p)) i j) hH
    simp only [SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.mapMatrix_apply,
      Matrix.map_apply, SpecialLinearGroup.coe_one] at hij
    have h0 : ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) (((H : 𝕄) - 1) i j) = 0 := by
      rw [Matrix.sub_apply, map_sub, hij, sub_eq_zero]
      rcases eq_or_ne i j with rfl | hne
      · simp
      · simp [Matrix.one_apply_ne hne]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨c, hc⟩ := h0
    refine ⟨c, ?_⟩
    rw [← ZMod.natCast_zmod_val (((H : 𝕄) - 1) i j), hc, Nat.cast_mul]
  choose X hX using hentry
  have hHX : (H : 𝕄) = 1 + (p : 𝕄) * of (fun i j => (X i j : ZMod (p ^ (k + 1)))) := by
    rw [← sub_eq_iff_eq_add', ← Matrix.diagonal_natCast]
    ext i j
    rw [hX i j, Matrix.diagonal_mul, of_apply]

  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ[X],
      (1 + C (p : ℤ) * Polynomial.X) ^ p ^ k - 1 = ((p ^ (k + 1) : ℕ) : ℤ[X]) * Q := by
    have h := dvd_sub_pow_of_dvd_sub (p := p) (a := 1 + C (p : ℤ) * Polynomial.X) (b := 1)
      ⟨C 1 * Polynomial.X, by simp⟩ k
    rw [one_pow] at h
    obtain ⟨Q, hQ⟩ := h
    exact ⟨Q, by rw [hQ]; norm_cast⟩

  set Xm : 𝕄 := of fun i j => (X i j : ZMod (p ^ (k + 1)))
  have heval := congrArg (Polynomial.aeval (R := ℤ) Xm) hQ
  simp only [map_sub, map_pow, map_add, map_one, map_mul, aeval_X, map_natCast] at heval

  have hzero : ((p ^ (k + 1) : ℕ) : 𝕄) = 0 := by
    rw [← map_natCast (algebraMap (ZMod (p ^ (k + 1))) 𝕄), ZMod.natCast_self, map_zero]
  rw [hzero, zero_mul, sub_eq_zero, ← hHX] at heval
  exact Subtype.ext (by rw [sl2coeZ_pow, heval, sl2coeZ_one])

theorem pow_twelve_mul_eq_one_SL2_ZMod_prime_pow {p : ℕ} (hp : p = 2 ∨ p = 3) (n : ℕ)
    (g : SL(2, ZMod (p ^ n))) : g ^ (12 * p ^ n) = 1 := by
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl; exacts [Nat.prime_two, Nat.prime_three]⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact Subtype.ext (Subsingleton.elim _ _)
  · have h12 : SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) (g ^ 12) = 1 := by
      rw [map_pow, pow_twelve_eq_one_SL2_ZMod hp]
    have := pow_eq_one_of_map_castHom_eq_one hn.ne' (g ^ 12) h12
    rw [← pow_mul] at this
    rw [show 12 * p ^ n = 12 * p ^ (n - 1) * p by
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn], pow_mul, this, one_pow]

theorem prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow (a b : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card (SL(2, ZMod (2 ^ a * 3 ^ b)))) : ℓ = 2 ∨ ℓ = 3 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (2 ^ a * 3 ^ b) := ⟨by positivity⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd

  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := by
    exact Nat.Coprime.pow _ _ (by norm_num)
  set e := slZModMulEquiv hcop
  have h1 : (e x).1 ^ (12 * 2 ^ a) = 1 := pow_twelve_mul_eq_one_SL2_ZMod_prime_pow (Or.inl rfl) a _
  have h2 : (e x).2 ^ (12 * 3 ^ b) = 1 := pow_twelve_mul_eq_one_SL2_ZMod_prime_pow (Or.inr rfl) b _
  have hex : e x ^ (12 * 2 ^ a * (12 * 3 ^ b)) = 1 := by
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, pow_mul, h1, one_pow, Prod.fst_one]
    · rw [Prod.pow_snd, pow_mul', h2, one_pow, Prod.snd_one]
  have hx' : x ^ (12 * 2 ^ a * (12 * 3 ^ b)) = 1 := by
    apply e.injective
    rw [map_pow, hex, map_one]
  have hord : ℓ ∣ 12 * 2 ^ a * (12 * 3 ^ b) := by
    rw [← hx]; exact orderOf_dvd_of_pow_eq_one hx'

  have h23 : ∀ {u : ℕ}, ℓ ∣ 12 * u → ℓ ∣ u ∨ ℓ = 2 ∨ ℓ = 3 := by
    intro u hu
    rcases (Nat.Prime.dvd_mul hℓ).mp hu with h | h
    · have h12 : ℓ ∣ 2 ^ 2 * 3 := by norm_num at h ⊢; exact h
      rcases (Nat.Prime.dvd_mul hℓ).mp h12 with h | h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
          (hℓ.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h))
    · exact Or.inl h
  rcases (Nat.Prime.dvd_mul hℓ).mp hord with h | h
  · rcases h23 h with h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h))
    · exact Or.inl h
    · exact Or.inr h
  · rcases h23 h with h | h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h))
    · exact Or.inl h
    · exact Or.inr h

end SmallPrimes

section LargePrimes

theorem commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod_impl
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (m : ℕ) (hm : ∀ p : ℕ, p.Prime → p ∣ m → 5 ≤ p) :
    commutator (SL(2, ZMod m)) = ⊤ ∧ HasTrivialSchurMultiplier (SL(2, ZMod m)) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd (hm 2 Nat.prime_two (dvd_zero 2)) (by norm_num)
  | one =>
    haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
    haveI : Subsingleton (SL(2, ZMod 1)) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact ⟨Subsingleton.elim _ _, hasTrivialSchurMultiplier_of_subsingleton⟩
  | prime_pow p n hp' hn =>
    have h5 : 5 ≤ p := hm p hp' (dvd_pow_self p hn.ne')
    exact ⟨hP1 p n hp' h5 hn.ne', hP2 p n hp' h5 hn.ne'⟩
  | coprime a b ha hb hab iha ihb =>
    have ha' := iha fun p hp hpa => hm p hp (hpa.mul_right b)
    have hb' := ihb fun p hp hpb => hm p hp (hpb.mul_left a)
    set e := slZModMulEquiv hab
    refine ⟨commutator_eq_top_of_mulEquiv (commutator_prod_eq_top ha'.1 hb'.1) e, ?_⟩
    exact (hasTrivialSchurMultiplier_prod_of_perfect ha'.1 ha'.2 hb'.1 hb'.2).of_mulEquiv e

theorem five_le_of_prime_dvd_of_coprime {q m p : ℕ} (hq : q.Prime) (hmq : Nat.Coprime m q)
    (hm : Nat.Coprime m (q ^ 2 - 1)) (hp : p.Prime) (hpm : p ∣ m) : 5 ≤ p := by
  have hpq : ¬p ∣ q := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpm hmq) h
    exact hp.one_lt.ne' this
  have hpq1 : ¬p ∣ q ^ 2 - 1 := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpm hm) h
    exact hp.one_lt.ne' this

  have h6 : 2 ∣ q * (q ^ 2 - 1) ∧ 3 ∣ q * (q ^ 2 - 1) := by
    have hq1 : 1 ≤ q := hq.one_lt.le
    have hfac : q * (q ^ 2 - 1) = (q - 1) * q * (q + 1) := by
      zify [hq1, Nat.one_le_pow 2 q hq1]
      ring
    rw [hfac]
    constructor
    · rcases Nat.even_or_odd q with h | h
      · exact (h.two_dvd.mul_left _).mul_right _
      · have : Even (q + 1) := h.add_one
        exact this.two_dvd.mul_left _
    · have h3 : (q - 1) % 3 = 0 ∨ q % 3 = 0 ∨ (q + 1) % 3 = 0 := by omega
      rcases h3 with h | h | h
      · exact ((Nat.dvd_of_mod_eq_zero h).mul_right _).mul_right _
      · exact ((Nat.dvd_of_mod_eq_zero h).mul_left _).mul_right _
      · exact (Nat.dvd_of_mod_eq_zero h).mul_left _
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h6.1 with h | h
    · exact hpq h
    · exact hpq1 h
  have hp3 : p ≠ 3 := by
    rintro rfl
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h6.2 with h | h
    · exact hpq h
    · exact hpq1 h
  have h2 := hp.two_le
  have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
  omega

end LargePrimes

end Ihara

end Inl_A3_SL2ZModFacts

open scoped MatrixGroups in
theorem solution
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 →
      Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (m : ℕ) (hm : ∀ p : ℕ, p.Prime → p ∣ m → 5 ≤ p) :
    commutator (SL(2, ZMod m)) = ⊤ ∧ Ihara.HasTrivialSchurMultiplier (SL(2, ZMod m)) :=
  Ihara.commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod_impl hP1 hP2 m hm

end S_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
end P2MW
export P2MW.S_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod (solution)
