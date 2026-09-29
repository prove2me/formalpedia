-- Prove2me | solution 1 for NumberField.TateGlobal.compactSpace_normOneIdeleClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bf35cd11-5739-5369-96d0-852fcf9d4f05

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_Completion_Finite
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass

set_option autoImplicit false
set_option Elab.async false

section Fold_TateSDecomp

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.AdelicLevel IsDedekindDomain"

open scoped NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem one_mem_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (1 : AdeleRing (𝓞 F) F) ∈ integralOutside S :=
  fun v _ => (v.adicCompletionIntegers F).one_mem

theorem mul_mem_integralOutside {S : Finset (HeightOneSpectrum (𝓞 F))} {x y : AdeleRing (𝓞 F) F}
    (hx : x ∈ integralOutside S) (hy : y ∈ integralOutside S) : x * y ∈ integralOutside S :=
  fun v hv => mul_mem (hx v hv) (hy v hv)

def unitsOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (AdeleRing (𝓞 F) F)ˣ where
  carrier := {x | (x : AdeleRing (𝓞 F) F) ∈ integralOutside S ∧
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S}
  one_mem' := ⟨by simpa using one_mem_integralOutside S, by simpa using one_mem_integralOutside S⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · simpa using mul_mem_integralOutside hx hy
    · simpa [mul_inv_rev] using mul_mem_integralOutside hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨hx', by simpa using hx⟩

theorem mem_unitsOutside_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    x ∈ unitsOutside S ↔
      (∀ v ∉ S, ((x : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F) ∧
      (∀ v ∉ S, (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F) :=
  Iff.rfl

section CharTriviality

open Filter Topology

variable (x : (AdeleRing (𝓞 F) F)ˣ)

theorem inv_val_fst_eq_one (h1 : ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1) :
    (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 = 1 := by
  have h := congrArg Prod.fst x.mul_inv
  change (x : AdeleRing (𝓞 F) F).1 * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
    = (1 : InfiniteAdeleRing F) at h
  rw [h1, one_mul] at h
  exact h

end CharTriviality

end NumberField.TateGlobal

end

end Fold_TateSDecomp

section Fold_ValuationOrd

set_option Elab.async false

set_option autoImplicit false

namespace M4aLocalCFT

namespace ValuationOrd

open Ideal IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L) [IsDiscreteValuationRing A]

private theorem exists_span_eq_pow {a : A} (ha : a ≠ 0) :
    ∃ n, span {a} = maximalIdeal A ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [span_singleton_eq_span_singleton.mpr hn, ← span_singleton_pow, ← hϖ.maximalIdeal_eq]

private theorem pow_maximalIdeal_ne_of_lt {n k : ℕ} (h : n < k) :
    (maximalIdeal A) ^ n ≠ maximalIdeal A ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro heq
  have hmem : ϖ ^ n ∈ maximalIdeal A ^ k := by
    rw [← heq, hϖ.maximalIdeal_eq, span_singleton_pow]
    exact mem_span_singleton_self _
  rw [hϖ.maximalIdeal_eq, span_singleton_pow, mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h1 : (1 : A) = ϖ ^ (k - n) * c := by
    refine mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) ?_
    rw [mul_one, ← mul_assoc, ← pow_add]
    rw [show n + (k - n) = k from by omega]
    exact hc
  have hkn : k - n - 1 + 1 = k - n := by omega
  exact hϖ.not_isUnit (isUnit_of_dvd_one ⟨ϖ ^ (k - n - 1) * c, by
    rw [h1, ← mul_assoc, ← pow_succ', hkn]⟩)

private theorem pow_maximalIdeal_injective {n k : ℕ}
    (h : (maximalIdeal A) ^ n = maximalIdeal A ^ k) : n = k := by
  rcases Nat.lt_trichotomy n k with hlt | heq | hgt
  · exact absurd h (pow_maximalIdeal_ne_of_lt A hlt)
  · exact heq
  · exact absurd h.symm (pow_maximalIdeal_ne_of_lt A hgt)

open Classical in
private noncomputable def ordA (a : A) : ℕ :=
  if h : a = 0 then 0 else (exists_span_eq_pow A h).choose

private theorem ordA_span {a : A} (ha : a ≠ 0) :
    span {a} = maximalIdeal A ^ ordA A a := by
  classical
  rw [ordA, dif_neg ha]
  exact (exists_span_eq_pow A ha).choose_spec

private theorem ordA_unique {a : A} (ha : a ≠ 0) {n : ℕ}
    (h : span {a} = maximalIdeal A ^ n) : ordA A a = n :=
  pow_maximalIdeal_injective A ((ordA_span A ha).symm.trans h)

private theorem ordA_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordA A (a * b) = ordA A a + ordA A b := by
  refine ordA_unique A (mul_ne_zero ha hb) ?_
  rw [← span_singleton_mul_span_singleton, ordA_span A ha, ordA_span A hb, pow_add]

open Classical in
private noncomputable def ordZ (x : Lˣ) : ℤ :=
  if h : (x : L) ∈ A then (ordA A ⟨(x : L), h⟩ : ℤ)
  else -(ordA A ⟨((x⁻¹ : Lˣ) : L), by
    rw [Units.val_inv_eq_inv_val]
    exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ : ℤ)

omit [IsDiscreteValuationRing ↥A] in
private theorem coe_mk_ne_zero (x : Lˣ) {y : L} (hy : y ∈ A) (hxy : y = (x : L)) :
    (⟨y, hy⟩ : A) ≠ 0 := by
  intro h0
  have : y = 0 := congrArg Subtype.val h0
  exact x.ne_zero (hxy ▸ this)

private theorem ordZ_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) : ordZ A x = (ordA A a : ℤ) - ordA A b := by
  classical
  by_cases h : (x : L) ∈ A
  · rw [ordZ, dif_pos h]
    have hab : (⟨(x : L), h⟩ : A) * b = a := Subtype.ext hx
    have hmul := ordA_mul A (coe_mk_ne_zero A x h rfl) hb
    rw [hab] at hmul
    omega
  · rw [ordZ, dif_neg h]
    set c : A := ⟨((x⁻¹ : Lˣ) : L), by
      rw [Units.val_inv_eq_inv_val]
      exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ with hc
    have hcx : (c : A) ≠ 0 := coe_mk_ne_zero A x⁻¹ _ rfl
    have hab : a * c = b := by
      refine Subtype.ext ?_
      push_cast
      have hcL : (c : L) = ((x : L))⁻¹ := by rw [hc]; exact Units.val_inv_eq_inv_val x
      rw [hcL, ← hx, mul_comm ((x : L)) ((b : L)), mul_assoc,
        mul_inv_cancel₀ x.ne_zero, mul_one]
    have hmul := ordA_mul A ha hcx
    rw [hab] at hmul
    omega

omit [IsDiscreteValuationRing ↥A] in
private theorem exists_rep (x : Lˣ) :
    ∃ a b : A, a ≠ 0 ∧ b ≠ 0 ∧ (x : L) * (b : L) = (a : L) := by
  rcases A.mem_or_inv_mem (x : L) with h | h
  · exact ⟨⟨(x : L), h⟩, 1, coe_mk_ne_zero A x h rfl, one_ne_zero, by
      push_cast; exact mul_one _⟩
  · refine ⟨1, ⟨((x⁻¹ : Lˣ) : L), by rwa [Units.val_inv_eq_inv_val]⟩,
      one_ne_zero, coe_mk_ne_zero A x⁻¹ _ rfl, ?_⟩
    show (x : L) * ((x⁻¹ : Lˣ) : L) = (1 : L)
    exact x.mul_inv

noncomputable def ord : Additive Lˣ →+ ℤ where
  toFun x := ordZ A x.toMul
  map_zero' := by
    show ordZ A (1 : Lˣ) = 0
    have h1 := ordZ_spec A (x := 1) (a := 1) (b := 1) one_ne_zero one_ne_zero
      (by rw [Units.val_one, one_mul])
    rw [h1]
    ring
  map_add' x y := by
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x.toMul
    obtain ⟨c, d, hc, hd, hy⟩ := exists_rep A y.toMul
    have hxy : (((x + y).toMul : Lˣ) : L) * ((b * d : A) : L) = ((a * c : A) : L) := by
      push_cast
      calc (x.toMul : L) * (y.toMul : L) * ((b : L) * (d : L))
          = ((x.toMul : L) * (b : L)) * ((y.toMul : L) * (d : L)) := by ring
        _ = (a : L) * (c : L) := by rw [hx, hy]
    show ordZ A (x + y).toMul = ordZ A x.toMul + ordZ A y.toMul
    rw [ordZ_spec A (mul_ne_zero ha hc) (mul_ne_zero hb hd) hxy,
      ordZ_spec A ha hb hx, ordZ_spec A hc hd hy, ordA_mul A ha hc, ordA_mul A hb hd]
    push_cast
    ring

theorem ord_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) {na nb : ℕ}
    (hna : span {a} = maximalIdeal A ^ na) (hnb : span {b} = maximalIdeal A ^ nb) :
    ord A (.ofMul x) = (na : ℤ) - nb := by
  have := ordZ_spec A ha hb hx
  rw [ordA_unique A ha hna, ordA_unique A hb hnb] at this
  exact this

theorem ord_ofMul_of_mem {x : Lˣ} (hx : (x : L) ∈ A) {n : ℕ}
    (hspan : span {(⟨(x : L), hx⟩ : A)} = maximalIdeal A ^ n) :
    ord A (.ofMul x) = n := by
  have h := ord_spec A (coe_mk_ne_zero A x hx rfl) one_ne_zero
    (b := 1) (by push_cast; exact mul_one _) hspan
    (by rw [span_singleton_eq_top.mpr isUnit_one, pow_zero, one_eq_top])
  simpa using h

theorem ord_ofMul_mk0_of_irreducible {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : A) : L) ≠ 0) :
    ord A (.ofMul (Units.mk0 ((ϖ : A) : L) h0)) = 1 := by
  refine ord_ofMul_of_mem A (x := Units.mk0 ((ϖ : A) : L) h0) (ϖ : A).2 ?_
  have hmk : (⟨((Units.mk0 ((ϖ : A) : L) h0 : Lˣ) : L), (ϖ : A).2⟩ : A) = ϖ :=
    Subtype.ext rfl
  rw [hmk, pow_one, ← hϖ.maximalIdeal_eq]

theorem ord_eq_zero_iff (x : Lˣ) :
    ord A (.ofMul x) = 0 ↔ x ∈ (Units.map (A.subtype.toMonoidHom)).range := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x
    have hspec : ordZ A x = (ordA A a : ℤ) - ordA A b := ordZ_spec A ha hb hx
    have h0 : ordZ A x = 0 := h
    have hord : ordA A a = ordA A b := by omega
    have hassoc : Associated a b := span_singleton_eq_span_singleton.mp
      (by rw [ordA_span A ha, ordA_span A hb, hord])
    obtain ⟨u, hu⟩ := hassoc
    have haL : (a : L) ≠ 0 := fun hz => ha (Subtype.ext hz)
    have hab : (a : L) * (((u : Aˣ) : A) : L) = (b : L) := by
      exact_mod_cast congrArg (fun s : A => (s : L)) hu
    have h1 : (x : L) * (((u : Aˣ) : A) : L) = 1 := by
      have h2 : (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) = (a : L) := by
        rw [hab]; exact hx
      have h3 : ((x : L) * (((u : Aˣ) : A) : L)) * (a : L) = 1 * (a : L) := by
        rw [one_mul]
        calc ((x : L) * (((u : Aˣ) : A) : L)) * (a : L)
            = (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) := by ring
          _ = (a : L) := h2
      exact mul_right_cancel₀ haL h3
    have huL : (((u : Aˣ) : A) : L) * (((u⁻¹ : Aˣ) : A) : L) = 1 := by
      exact_mod_cast congrArg (fun s : A => (s : L)) u.mul_inv
    have hxinv : (x : L) = ((((u : Aˣ) : A) : L))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have huinv : (((u⁻¹ : Aˣ) : A) : L) = ((((u : Aˣ) : A) : L))⁻¹ :=
      eq_inv_of_mul_eq_one_right huL
    refine ⟨u⁻¹, Units.ext ?_⟩
    show (((u⁻¹ : Aˣ) : A) : L) = (x : L)
    rw [huinv, hxinv]
  · rintro ⟨u, rfl⟩
    have hmem : ((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L) ∈ A := by
      show ((A.subtype) ((u : Aˣ) : A) : L) ∈ A
      exact ((u : Aˣ) : A).2
    have hspan : span {(⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A)}
        = maximalIdeal A ^ 0 := by
      rw [show (⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A) = ((u : Aˣ) : A)
        from Subtype.ext rfl]
      rw [span_singleton_eq_top.mpr u.isUnit, pow_zero, one_eq_top]
    have := ord_ofMul_of_mem A hmem hspan
    simpa using this

end ValuationOrd

end M4aLocalCFT

end Fold_ValuationOrd

section Fold_TateSDecomp2

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.AdelicLevel IsDedekindDomain"

open scoped NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

def unitAtHom (w : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* (w.adicCompletion F)ˣ :=
  Units.map (((finAdeleEval (𝓞 F) F w).comp (adeleFin (𝓞 F) F)).toMonoidHom)

theorem unitAtHom_val (x : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    (unitAtHom w x : w.adicCompletion F) = ((x : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w :=
  rfl

def embUnit (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v)

theorem embUnit_val_fst (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := rfl

theorem unitAtHom_embUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    unitAtHom v (embUnit v t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F v t)

theorem unitAtHom_embUnit_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (t : (v.adicCompletion F)ˣ) :
    unitAtHom w (embUnit v t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F v t hw)

def ordAt (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : ℤ :=
  M4aLocalCFT.ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul t)

theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (s t : (v.adicCompletion F)ˣ) :
    ordAt v (s * t) = ordAt v s + ordAt v t := by
  simp [ordAt, ofMul_mul, map_add]

theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt v (1 : (v.adicCompletion F)ˣ) = 0 := by
  simp [ordAt]

theorem ordAt_zpow (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) (n : ℤ) :
    ordAt v (t ^ n) = n * ordAt v t := by
  simp [ordAt, ofMul_zpow, map_zsmul]

theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ordAt v t = 0 ↔ (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  rw [ordAt, M4aLocalCFT.ValuationOrd.ord_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu]
    exact ⟨(u : v.adicCompletionIntegers F).2, ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨⟨_, h⟩, ⟨_, h'⟩, Subtype.ext t.mul_inv, Subtype.ext t.inv_mul⟩, Units.ext rfl⟩

structure Uniformizers (F : Type) [Field F] [NumberField F] where
  ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ
  ordAt_eq_one : ∀ v, ordAt v (ϖ v) = 1

def unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : (AdeleRing (𝓞 F) F)ˣ :=
  k.prod fun v n => embUnit v (ϖ.ϖ v) ^ n

theorem unitAtHom_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) (w : HeightOneSpectrum (𝓞 F)) :
    unitAtHom w (unifPow ϖ k) = ϖ.ϖ w ^ k w := by
  classical
  rw [unifPow, Finsupp.prod, map_prod]
  simp_rw [map_zpow]
  rw [Finset.prod_eq_single w]
  · rw [unitAtHom_embUnit_self]
  · intro v _ hvw
    rw [unitAtHom_embUnit_of_ne (Ne.symm hvw), one_zpow]
  · intro hw
    rw [Finsupp.notMem_support_iff.mp hw, zpow_zero]

theorem ordAt_unitAtHom_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (w : HeightOneSpectrum (𝓞 F)) : ordAt w (unitAtHom w (unifPow ϖ k)) = k w := by
  rw [unitAtHom_unifPow, ordAt_zpow, ϖ.ordAt_eq_one, mul_one]

theorem finite_setOf_ordAt_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | ordAt v (unitAtHom v x) ≠ 0}.Finite := by
  have h1 := (((x : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F).2)
  have h2 := ((((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F).2)
  have h := Filter.eventually_cofinite.mp (h1.and h2)
  refine h.subset fun v hv => ?_
  intro hv'
  apply hv
  rw [ordAt_eq_zero_iff]
  exact hv'

def expVec (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) : HeightOneSpectrum (𝓞 F) →₀ ℤ := by
  classical
  exact Finsupp.ofSupportFinite (fun v => if v ∈ S then 0 else ordAt v (unitAtHom v x))
    ((finite_setOf_ordAt_ne_zero x).subset fun v hv => by
      simp only [Function.mem_support, ne_eq, ite_eq_left_iff, Classical.not_imp] at hv
      exact hv.2)

theorem expVec_apply_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : expVec S x v = ordAt v (unitAtHom v x) := by
  classical
  simp [expVec, Finsupp.ofSupportFinite_coe, hv]

def archUnits : (AdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ := Units.map (adeleArch (𝓞 F) F).toMonoidHom

end NumberField.TateGlobal

end

end Fold_TateSDecomp2

section Fold_LocalHaarModulus

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open scoped NNReal ENNReal Pointwise

namespace M4aLocalCFT

namespace LocalHaarModulus

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem card_residueField_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField F v).toEquiv.symm

section CosetStep

variable {F v}

theorem exists_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (Y : v.adicCompletionIntegers F) :
    ∃ z : v.adicCompletionIntegers F,
      Y = Quotient.out (residue (v.adicCompletionIntegers F) Y) + ϖ * z := by
  have hout : residue (v.adicCompletionIntegers F)
      (Quotient.out (residue (v.adicCompletionIntegers F) Y))
      = residue (v.adicCompletionIntegers F) Y := Quotient.out_eq _
  have hzero : residue (v.adicCompletionIntegers F)
      (Y - Quotient.out (residue (v.adicCompletionIntegers F) Y)) = 0 := by
    rw [map_sub, hout, sub_self]
  set w : v.adicCompletionIntegers F
      := Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) with hw
  have hmem : w ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hsub : Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) = ϖ * z := by
    rw [← hw]; exact hz
  exact sub_eq_iff_eq_add'.mp hsub

theorem residue_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (k : ResidueField (v.adicCompletionIntegers F)) (z : v.adicCompletionIntegers F) :
    residue (v.adicCompletionIntegers F) (Quotient.out k + ϖ * z) = k := by
  have hϖ0 : residue (v.adicCompletionIntegers F) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  have hout : residue (v.adicCompletionIntegers F) (Quotient.out k) = k := Quotient.out_eq _
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, hout]

abbrev cosetMap (ϖ : v.adicCompletionIntegers F)
    (k : ResidueField (v.adicCompletionIntegers F)) (y : v.adicCompletion F) :
    v.adicCompletion F :=
  ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
    + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * y

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem integers_eq_iUnion_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := exists_out_add_mul hϖ (⟨y, hy⟩ : v.adicCompletionIntegers F)
    refine mem_iUnion.mpr ⟨residue (v.adicCompletionIntegers F) ⟨y, hy⟩, ?_⟩
    refine ⟨(z : v.adicCompletion F), z.2, ?_⟩
    have hco := congrArg
      (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at hco
    exact hco.symm
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzy⟩ := hk
    obtain ⟨X, hXy⟩ : ∃ X : v.adicCompletionIntegers F, (X : v.adicCompletion F) = y :=
      ⟨Quotient.out k + ϖ * ⟨z, hz⟩, by push_cast; exact hzy⟩
    rw [← hXy]
    exact X.2

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem pairwise_disjoint_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint fun k : ResidueField (v.adicCompletionIntegers F) =>
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun y hy hy' => hkk' ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  have hKeq : ((Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F) :
      v.adicCompletion F)
      = ((Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :
          v.adicCompletion F) := by
    push_cast
    rw [show ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z = y from hzy,
        show ((Quotient.out k' : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z' = y from hzy']
  have hAeq : (Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F)
      = (Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :=
    Subtype.coe_injective hKeq
  have := congrArg (residue (v.adicCompletionIntegers F)) hAeq
  rwa [residue_out_add_mul hϖ, residue_out_add_mul hϖ] at this

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem cosetMap_image_eq {ϖ : v.adicCompletionIntegers F}
    (k : ResidueField (v.adicCompletionIntegers F)) :
    cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
          (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_comp]
  rfl

end CosetStep

section Measure

variable {F v}

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have hϖ0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  have hTopen : IsOpen (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (NumberField.isOpenAdicCompletionIntegers F v).smul₀ hϖ0
  have hTmeas := hTopen.measurableSet
  have hbridge : ∀ k : ResidueField (v.adicCompletionIntegers F),
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun k => cosetMap_image_eq k
  calc μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = μ (⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        rw [← integers_eq_iUnion_image hϖ]
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine measure_iUnion ?_ fun k => ?_
        · intro k k' hkk'
          exact pairwise_disjoint_image hϖ hkk'
        · rw [hbridge k]
          exact hTmeas.const_vadd _
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := by
        exact tsum_congr fun k => by rw [hbridge k]
    _ = ∑' _ : ResidueField (v.adicCompletionIntegers F),
          μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine tsum_congr fun k => ?_
        exact measure_vadd _ _ _
    _ = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]

end Measure

section MainTheorem

variable {F v}

theorem distribHaarChar_eq_one_of_mem_range (x : (v.adicCompletion F)ˣ)
    (hx : x ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range) :
    distribHaarChar (v.adicCompletion F) x = 1 := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  obtain ⟨u, rfl⟩ := hx
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  obtain ⟨μ⟩ : Nonempty {μ : Measure (v.adicCompletion F) // μ.IsAddHaarMeasure ∧ μ.Regular} :=
    ⟨⟨(MeasureTheory.Measure.addHaarMeasure
        ⟨⟨S, hK⟩, by
          rw [interior_eq_iff_isOpen.mpr hO]
          exact ⟨0, Subring.zero_mem _⟩⟩),
      inferInstance, inferInstance⟩⟩
  obtain ⟨μ, hHaar, hReg⟩ := μ
  haveI := hHaar; haveI := hReg
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S)
    (hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩) (hK.measure_lt_top.ne) ?_
  have hset : ((Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)) u : _) • S = S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mul_mem ((u : v.adicCompletionIntegers F).2) hz
    · intro hy
      set w : v.adicCompletionIntegers F := ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
        v.adicCompletionIntegers F) with hw
      refine ⟨(w : v.adicCompletion F) * y, mul_mem w.2 hy, ?_⟩
      have hcancel : ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * (w : v.adicCompletion F) = 1 := by
        have : ((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F)
            = (1 : v.adicCompletionIntegers F) := by
          rw [hw]
          exact_mod_cast u.mul_inv
        calc ((u : v.adicCompletionIntegers F) : v.adicCompletion F) * (w : v.adicCompletion F)
            = (((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F) :
                v.adicCompletion F) := by rw [Subring.coe_mul]
          _ = 1 := by rw [this]; rfl
      show ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * ((w : v.adicCompletion F) * y) = y
      rw [← mul_assoc, hcancel, one_mul]
  rw [hset, ENNReal.coe_one, one_mul]

theorem distribHaarChar_mk0_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0) :
    distribHaarChar (v.adicCompletion F) (Units.mk0 _ h0)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  set μ : Measure (v.adicCompletion F) := MeasureTheory.Measure.addHaarMeasure
    ⟨⟨S, hK⟩, by
      rw [interior_eq_iff_isOpen.mpr hO]
      exact ⟨0, Subring.zero_mem _⟩⟩ with hμ
  have hq0 : (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos
  have hS0 : μ S ≠ 0 := hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩
  have hSfin : μ S ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S) hS0 hSfin ?_
  have hcount := measure_integers_eq_card_mul μ hϖ
  show μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) • S)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ * μ S
  rw [ENNReal.coe_inv (by exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos), ENNReal.coe_natCast]
  rw [hcount]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 (ENNReal.natCast_ne_top _), one_mul]

theorem distribHaarChar_adicCompletion (x : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) x
      = ((Ideal.absNorm v.asIdeal : ℝ≥0))
          ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  set w : (v.adicCompletion F)ˣ := Units.mk0 _ h0 with hw
  set k : ℤ := ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) with hk
  set y : (v.adicCompletion F)ˣ := x * w ^ (-k) with hy
  have hordw : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 1 :=
    ValuationOrd.ord_ofMul_mk0_of_irreducible (v.adicCompletionIntegers F) hϖ h0
  have hordy : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul y) = 0 := by
    have hmul : Additive.ofMul y = Additive.ofMul x + (-k) • Additive.ofMul w := rfl
    rw [hmul, map_add, map_zsmul, hordw, smul_eq_mul, mul_one, ← hk, add_neg_cancel]
  have hyunit : distribHaarChar (v.adicCompletion F) y = 1 :=
    distribHaarChar_eq_one_of_mem_range y
      ((ValuationOrd.ord_eq_zero_iff (v.adicCompletionIntegers F) y).mp hordy)
  have hxy : x = y * w ^ k := by
    rw [hy, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hqw : distribHaarChar (v.adicCompletion F) w
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ :=
    distribHaarChar_mk0_irreducible hϖ h0
  rw [hxy, map_mul, map_zpow, hyunit, one_mul, hqw, inv_zpow, ← zpow_neg,
    card_residueField_eq_absNorm]

theorem measure_smul_integers [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] [μ.Regular] (x : (v.adicCompletion F)ˣ) :
    μ ((x : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (((Ideal.absNorm v.asIdeal : ℝ≥0))
          ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) : ℝ≥0)
        * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [← distribHaarChar_adicCompletion, distribHaarChar_mul]
  rfl

end MainTheorem

end

end LocalHaarModulus

end M4aLocalCFT

end Fold_LocalHaarModulus

section Fold_LocalZetaUnramified

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

section Shells

variable {ϖ : v.adicCompletionIntegers F}

theorem coe_ne_zero_of_irreducible (hϖ : Irreducible ϖ) :
    ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
  fun h => hϖ.ne_zero (Subtype.ext h)

def piUnit (hϖ : Irreducible ϖ) : (v.adicCompletion F)ˣ := Units.mk0 _ (coe_ne_zero_of_irreducible hϖ)

@[scoped simp] theorem piUnit_val (hϖ : Irreducible ϖ) :
    ((piUnit hϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) := rfl

theorem ord_piUnit (hϖ : Irreducible ϖ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ)) = 1 :=
  ValuationOrd.ord_ofMul_mk0_of_irreducible _ hϖ _

end Shells

section Measures

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end Measures

section Integrand

variable {ϖ : v.adicCompletionIntegers F}

end Integrand

section Zeta

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end Zeta

end LocalZetaUnramified
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_LocalZetaUnramified
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_MulHaarFromAdditive

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace MulHaarFromAdditive

open LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

variable {ϖ : v.adicCompletionIntegers F}

theorem ord_ofMul_mul (u w : (v.adicCompletion F)ˣ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (u * w))
      = ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u)
        + ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) := by
  have h : Additive.ofMul (u * w) = Additive.ofMul u + Additive.ofMul w := rfl
  rw [h, map_add]

theorem ord_ofMul_zpow_piUnit (hϖ : Irreducible ϖ) (k : ℤ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ ^ k)) = k := by
  have h : Additive.ofMul (piUnit hϖ ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_zsmul, ord_piUnit hϖ, smul_eq_mul, mul_one]

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

variable [MeasurableSpace ((v.adicCompletion F)ˣ)] [BorelSpace ((v.adicCompletion F)ˣ)]

end MulHaarFromAdditive
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_MulHaarFromAdditive
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_ValuedOrdBridge

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open WithZero Multiplicative

open scoped NNReal ENNReal

noncomputable section

namespace M4aLocalCFT

namespace ValuedOrdBridge

open LocalZetaUnramified MulHaarFromAdditive

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem valued_ne_zero_of_ne_zero {x : v.adicCompletion F} (hx : x ≠ 0) :
    Valued.v x ≠ 0 := by
  intro h0
  have h1 : Valued.v x * Valued.v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem valued_le_one_of_mem {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v x ≤ 1 :=
  hx

theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Integers (v.adicCompletionIntegers F) :=
  Valuation.valuationSubring.integers _

theorem exists_irreducible_valued :
    ∃ ϖ : v.adicCompletionIntegers F, Irreducible ϖ ∧
      Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
        = WithZero.exp (-1 : ℤ) := by
  obtain ⟨y, hy⟩ := valuedAdicCompletion_surjective (K := F) (v := v) (WithZero.exp (-1 : ℤ))
  have hy1 : y ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, hy, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  refine ⟨⟨y, hy1⟩, ⟨?_, ?_⟩, hy⟩
  ·
    intro hu
    have h1 := (integers_adicCompletionIntegers (v := v)).one_of_isUnit hu
    rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) ⟨y, hy1⟩ = y
      from rfl, hy] at h1
    exact absurd ((WithZero.exp_eq_one).mp h1) (by norm_num)
  ·
    rintro a b hab
    have hane : (a : v.adicCompletion F) ≠ 0 := by
      intro h0
      apply hy0
      have : y = (a : v.adicCompletion F) * (b : v.adicCompletion F) := by
        simpa using congrArg Subtype.val hab
      rw [this, h0, zero_mul]
    have hbne : (b : v.adicCompletion F) ≠ 0 := by
      intro h0
      apply hy0
      have : y = (a : v.adicCompletion F) * (b : v.adicCompletion F) := by
        simpa using congrArg Subtype.val hab
      rw [this, h0, mul_zero]
    have hmul : Valued.v ((a : v.adicCompletion F)) * Valued.v ((b : v.adicCompletion F))
        = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul]
      have : (a : v.adicCompletion F) * (b : v.adicCompletion F) = y := by
        simpa using (congrArg Subtype.val hab).symm
      rw [this, hy]
    have hva0 : Valued.v ((a : v.adicCompletion F)) ≠ 0 := by
      exact valued_ne_zero_of_ne_zero hane
    have hvb0 : Valued.v ((b : v.adicCompletion F)) ≠ 0 := by
      exact valued_ne_zero_of_ne_zero hbne
    set s : ℤ := WithZero.log (Valued.v ((a : v.adicCompletion F))) with hs
    set t : ℤ := WithZero.log (Valued.v ((b : v.adicCompletion F))) with ht
    have hexps : Valued.v ((a : v.adicCompletion F)) = WithZero.exp s :=
      (WithZero.exp_log hva0).symm
    have hexpt : Valued.v ((b : v.adicCompletion F)) = WithZero.exp t :=
      (WithZero.exp_log hvb0).symm
    have hsum : s + t = -1 := by
      have := hmul
      rw [hexps, hexpt, ← WithZero.exp_add] at this
      exact WithZero.exp_inj.mp this
    have hsle : s ≤ 0 := by
      have := valued_le_one_of_mem a.2
      rw [hexps, ← WithZero.exp_zero] at this
      exact WithZero.exp_le_exp.mp this
    have htle : t ≤ 0 := by
      have := valued_le_one_of_mem b.2
      rw [hexpt, ← WithZero.exp_zero] at this
      exact WithZero.exp_le_exp.mp this
    rcases (by omega : s = 0 ∨ t = 0) with h0 | h0
    · left
      refine (integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := a) ?_
      rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) a
        = (a : v.adicCompletion F) from rfl, hexps, h0, WithZero.exp_zero]
    · right
      refine (integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := b) ?_
      rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) b
        = (b : v.adicCompletion F) from rfl, hexpt, h0, WithZero.exp_zero]

variable {ϖ : v.adicCompletionIntegers F}

theorem valued_coe_of_irreducible (hϖ : Irreducible ϖ) :
    Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀, hv₀⟩ := exists_irreducible_valued (v := v)
  have hϖK : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
    coe_ne_zero_of_irreducible hϖ
  have hϖv0 : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    exact valued_ne_zero_of_ne_zero hϖK
  have hle : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    valued_le_one_of_mem ϖ.2
  have hne1 : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 1 := by
    intro h1
    exact hϖ.not_isUnit ((integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := ϖ) h1)
  set s : ℤ := WithZero.log
    (Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)) with hs
  have hexps : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      = WithZero.exp s := (WithZero.exp_log hϖv0).symm
  have hsle : s ≤ 0 := by
    have := hle
    rw [hexps, ← WithZero.exp_zero] at this
    exact WithZero.exp_le_exp.mp this
  have hsne : s ≠ 0 := by
    intro h0
    exact hne1 (by rw [hexps, h0, WithZero.exp_zero])
  have hlev : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      ≤ Valued.v ((π₀ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hexps, hv₀]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hdvd : π₀ ∣ ϖ :=
    ((integers_adicCompletionIntegers (v := v)).le_iff_dvd (x := ϖ) (y := π₀)).mp hlev
  obtain ⟨c, hc⟩ := hdvd
  rcases hϖ.isUnit_or_isUnit hc with hu | hu
  · exact absurd hu hπ₀.not_isUnit
  · have h1 : Valued.v ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      have := (integers_adicCompletionIntegers (v := v)).one_of_isUnit hu
      rwa [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) c
        = (c : v.adicCompletion F) from rfl] at this
    have hcoe : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
        = ((π₀ : v.adicCompletionIntegers F) : v.adicCompletion F)
          * ((c : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      simpa using congrArg Subtype.val hc
    rw [hcoe, map_mul, hv₀, h1, mul_one]

theorem valued_coe_units_eq_exp_neg_ord (x : (v.adicCompletion F)ˣ) :
    Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) := by
  obtain ⟨π₀, hπ₀, hv₀⟩ := exists_irreducible_valued (v := v)
  set n : ℤ := ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) with hn
  set u : (v.adicCompletion F)ˣ := (piUnit hπ₀ ^ n)⁻¹ * x with hu
  have hordu : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u) = 0 := by
    rw [hu, ord_ofMul_mul,
      show ((piUnit hπ₀ ^ n)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hπ₀ ^ (-n) from
        (zpow_neg _ _).symm,
      ord_ofMul_zpow_piUnit hπ₀, ← hn]
    omega
  obtain ⟨w, hw⟩ := (ValuationOrd.ord_eq_zero_iff (v.adicCompletionIntegers F) u).mp hordu
  have hvu : Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    have hiso : ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (w : _) := by
      rw [← hw]; rfl
    rw [hiso]
    exact (integers_adicCompletionIntegers (v := v)).one_of_isUnit w.isUnit
  have hx : (x : (v.adicCompletion F)ˣ) = piUnit hπ₀ ^ n * u := by
    rw [hu, mul_inv_cancel_left]
  have hvpi : Valued.v (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
      = WithZero.exp (-n) := by
    have hzpow : (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
        = (((piUnit hπ₀ : (v.adicCompletion F)ˣ)) : v.adicCompletion F) ^ n := by
      push_cast
      rfl
    rw [hzpow, map_zpow₀, piUnit_val, valued_coe_of_irreducible hπ₀,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]
  calc Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = Valued.v ((((piUnit hπ₀ ^ n * u : (v.adicCompletion F)ˣ)) : v.adicCompletion F)) := by
        rw [← hx]
    _ = Valued.v (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
        * Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
        rw [Units.val_mul, map_mul]
    _ = WithZero.exp (-n) := by rw [hvpi, hvu, mul_one]

end ValuedOrdBridge
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_ValuedOrdBridge
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_IdeleIdealClass

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal IsDedekindDomain FractionalIdeal"

open scoped nonZeroDivisors

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

def fracIdealAtUnit (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) (coeIdeal_ne_zero.mpr v.ne_bot)

theorem fracIdealAtUnit_val (v : HeightOneSpectrum (𝓞 F)) :
    (fracIdealAtUnit (F := F) v : FractionalIdeal (𝓞 F)⁰ F) = v.asIdeal := rfl

def fracIdealProd (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  exps.prod fun v k => fracIdealAtUnit v ^ k

theorem fracIdealProd_zero : fracIdealProd (F := F) 0 = 1 := by
  simp [fracIdealProd, Finsupp.prod_zero_index]

theorem fracIdealProd_add (e₁ e₂ : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    fracIdealProd (F := F) (e₁ + e₂) = fracIdealProd e₁ * fracIdealProd e₂ := by
  simp only [fracIdealProd]
  exact Finsupp.prod_add_index' (fun v => zpow_zero _) (fun v k₁ k₂ => zpow_add _ k₁ k₂)

def fracIdealProdHom : Multiplicative (HeightOneSpectrum (𝓞 F) →₀ ℤ) →* (FractionalIdeal (𝓞 F)⁰ F)ˣ where
  toFun e := fracIdealProd e.toAdd
  map_one' := fracIdealProd_zero
  map_mul' e₁ e₂ := fracIdealProd_add e₁.toAdd e₂.toAdd

theorem fracIdealProd_val (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    (fracIdealProd (F := F) exps : FractionalIdeal (𝓞 F)⁰ F)
      = exps.prod fun v k => (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ k := by
  simp only [fracIdealProd, Finsupp.prod]
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val, fracIdealAtUnit_val]

theorem count_fracIdealProd (v : HeightOneSpectrum (𝓞 F)) (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    count F v (fracIdealProd (F := F) exps : FractionalIdeal (𝓞 F)⁰ F) = exps v := by
  rw [fracIdealProd_val]
  exact count_finsuppProd F v exps

theorem fracIdealProd_eq_one_iff (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    fracIdealProd (F := F) exps = 1 ↔ exps = 0 := by
  constructor
  · intro h
    refine Finsupp.ext fun v => ?_
    have := count_fracIdealProd (F := F) v exps
    rw [h, Units.val_one, count_one] at this
    exact this.symm
  · intro h; rw [h]; exact fracIdealProd_zero

theorem expVec_one : expVec (F := F) ∅ 1 = 0 := by
  refine Finsupp.ext fun v => ?_
  rw [expVec_apply_of_not_mem 1 (Finset.notMem_empty v), map_one, ordAt_one]
  rfl

theorem expVec_mul (x y : (AdeleRing (𝓞 F) F)ˣ) :
    expVec (F := F) ∅ (x * y) = expVec ∅ x + expVec ∅ y := by
  refine Finsupp.ext fun v => ?_
  simp only [Finsupp.add_apply]
  rw [expVec_apply_of_not_mem _ (Finset.notMem_empty v),
    expVec_apply_of_not_mem _ (Finset.notMem_empty v),
    expVec_apply_of_not_mem _ (Finset.notMem_empty v), map_mul, ordAt_mul]

def expVecHom : (AdeleRing (𝓞 F) F)ˣ →* Multiplicative (HeightOneSpectrum (𝓞 F) →₀ ℤ) where
  toFun x := Multiplicative.ofAdd (expVec ∅ x)
  map_one' := by rw [expVec_one]; rfl
  map_mul' x y := by rw [expVec_mul]; rfl

theorem expVec_eq_zero_iff (x : (AdeleRing (𝓞 F) F)ˣ) :
    expVec (F := F) ∅ x = 0 ↔ x ∈ unitsOutside ∅ := by
  rw [mem_unitsOutside_iff]
  constructor
  · intro h
    refine ⟨fun v _ => ?_, fun v _ => ?_⟩
    · have h1 : ordAt v (unitAtHom v x) = 0 := by
        rw [← expVec_apply_of_not_mem x (Finset.notMem_empty v), h]; rfl
      exact ((ordAt_eq_zero_iff v _).mp h1).1
    · have h1 : ordAt v (unitAtHom v x) = 0 := by
        rw [← expVec_apply_of_not_mem x (Finset.notMem_empty v), h]; rfl
      have h2 := ((ordAt_eq_zero_iff v _).mp h1).2
      rwa [← map_inv] at h2
  · intro ⟨h1, h2⟩
    refine Finsupp.ext fun v => ?_
    rw [expVec_apply_of_not_mem x (Finset.notMem_empty v), Finsupp.zero_apply,
      ordAt_eq_zero_iff]
    refine ⟨h1 v (Finset.notMem_empty v), ?_⟩
    have := h2 v (Finset.notMem_empty v)
    rwa [← map_inv]

def ideleIdeal : (AdeleRing (𝓞 F) F)ˣ →* (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  fracIdealProdHom.comp expVecHom

theorem ideleIdeal_apply (x : (AdeleRing (𝓞 F) F)ˣ) :
    ideleIdeal x = fracIdealProd (expVec ∅ x) := rfl

theorem count_ideleIdeal (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) :
    count F v (ideleIdeal x : FractionalIdeal (𝓞 F)⁰ F) = ordAt v (unitAtHom v x) := by
  rw [ideleIdeal_apply, count_fracIdealProd, expVec_apply_of_not_mem x (Finset.notMem_empty v)]

theorem ideleIdeal_eq_one_iff (x : (AdeleRing (𝓞 F) F)ˣ) :
    ideleIdeal x = 1 ↔ x ∈ unitsOutside ∅ := by
  rw [ideleIdeal_apply, fracIdealProd_eq_one_iff, expVec_eq_zero_iff]

theorem ker_ideleIdeal : (ideleIdeal (F := F)).ker = unitsOutside ∅ := by
  ext x
  exact ideleIdeal_eq_one_iff x

def ideleClass : (AdeleRing (𝓞 F) F)ˣ →* ClassGroup (𝓞 F) :=
  (ClassGroup.mk F).comp ideleIdeal

theorem ideleIdeal_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ideleIdeal (unifPow ϖ k) = fracIdealProd k := by
  rw [ideleIdeal_apply]
  congr 1
  refine Finsupp.ext fun v => ?_
  rw [expVec_apply_of_not_mem _ (Finset.notMem_empty v), ordAt_unitAtHom_unifPow]

def countFinsupp (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => count F v (I : FractionalIdeal (𝓞 F)⁰ F))
    ((finite_factors (I : FractionalIdeal (𝓞 F)⁰ F)).subset fun v hv => by
      simp only [Function.mem_support, ne_eq] at hv ⊢
      exact hv)

theorem countFinsupp_apply (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    countFinsupp I v = count F v (I : FractionalIdeal (𝓞 F)⁰ F) := by
  simp [countFinsupp, Finsupp.ofSupportFinite_coe]

theorem fracIdealProd_countFinsupp (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    fracIdealProd (countFinsupp I) = I := by
  refine Units.ext ?_
  rw [fracIdealProd_val]
  have hI : (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := I.ne_zero
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization' (K := F) hI]
  rw [Finsupp.prod]
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (s := (countFinsupp I).support)]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [countFinsupp_apply]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, countFinsupp_apply]
    intro h
    rw [h, zpow_zero] at hv
    exact hv rfl

theorem ideleIdeal_surjective (ϖ : Uniformizers F) : Function.Surjective (ideleIdeal (F := F)) :=
  fun I => ⟨unifPow ϖ (countFinsupp I), (ideleIdeal_unifPow ϖ _).trans (fracIdealProd_countFinsupp I)⟩

theorem ideleClass_surjective (ϖ : Uniformizers F) : Function.Surjective (ideleClass (F := F)) := by
  have h1 : Function.Surjective
      (Units.map (canonicalEquiv (𝓞 F)⁰ F (FractionRing (𝓞 F))).toMonoidHom) :=
    (Units.mapEquiv (canonicalEquiv (𝓞 F)⁰ F (FractionRing (𝓞 F))).toMulEquiv).surjective
  exact (QuotientGroup.mk'_surjective _).comp (h1.comp (ideleIdeal_surjective ϖ))

def someUniformizers : Uniformizers F where
  ϖ v :=
    let ϖ := (M4aLocalCFT.ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose
    have hirr : Irreducible ϖ :=
      (M4aLocalCFT.ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose_spec.1
    have h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := fun h =>
      hirr.ne_zero (Subtype.ext h)
    Units.mk0 _ h0
  ordAt_eq_one v := by
    set ϖ := (M4aLocalCFT.ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose
    have hirr : Irreducible ϖ :=
      (M4aLocalCFT.ValuedOrdBridge.exists_irreducible_valued (F := F) (v := v)).choose_spec.1
    have h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := fun h =>
      hirr.ne_zero (Subtype.ext h)
    show ordAt v (Units.mk0 _ h0) = 1
    exact M4aLocalCFT.ValuationOrd.ord_ofMul_mk0_of_irreducible _ hirr h0

theorem ideleClass_surjective' : Function.Surjective (ideleClass (F := F)) :=
  ideleClass_surjective someUniformizers

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_IdeleIdealClass
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_IdeleIdealClass2

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal IsDedekindDomain FractionalIdeal WithZero"

open scoped nonZeroDivisors

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem unitAtHom_principal_val (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    ((unitAtHom v (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α) :
      (v.adicCompletion F)ˣ) : v.adicCompletion F) = ((α : F) : v.adicCompletion F) := by
  rw [unitAtHom_val]
  exact AdeleRing.algebraMap_snd_apply (𝓞 F) F (α : F) v

theorem valuation_eq_exp_neg_count_spanSingleton (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    v.valuation F (α : F) = WithZero.exp (-(count F v (spanSingleton (𝓞 F)⁰ (α : F)))) := by
  classical
  obtain ⟨n, d, hd, hmk⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (α : F)
  have hα : (α : F) ≠ 0 := α.ne_zero
  have hn : n ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hmk
    exact hα hmk.symm
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hI : (spanSingleton (𝓞 F)⁰ (α : F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rwa [ne_eq, spanSingleton_eq_zero_iff]
  have h_aJ : (spanSingleton (𝓞 F)⁰ (α : F) : FractionalIdeal (𝓞 F)⁰ F)
      = spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) d)⁻¹
        * ↑(Ideal.span {n} : Ideal (𝓞 F)) := by
    rw [coeIdeal_span_singleton, ← hmk, div_eq_inv_mul, ← spanSingleton_mul_spanSingleton]
  rw [count_well_defined (K := F) v hI h_aJ]
  have hmk' : IsLocalization.mk' F n (⟨d, hd⟩ : (𝓞 F)⁰) = (α : F) := by
    rw [IsFractionRing.mk'_eq_div]; exact hmk
  rw [← hmk', HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg hd0, ← WithZero.exp_sub, WithZero.exp_inj, neg_sub, neg_sub_neg]

theorem ordAt_unitAtHom_principal (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    ordAt v (unitAtHom v (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α))
      = count F v (spanSingleton (𝓞 F)⁰ (α : F)) := by
  rw [← neg_inj, ← WithZero.exp_inj]
  rw [show ordAt v (unitAtHom v _)
        = M4aLocalCFT.ValuationOrd.ord (v.adicCompletionIntegers F)
          (Additive.ofMul (unitAtHom v (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α)))
      from rfl]
  rw [← M4aLocalCFT.ValuedOrdBridge.valued_coe_units_eq_exp_neg_ord]
  rw [unitAtHom_principal_val, v.valuedAdicCompletion_eq_valuation' (α : F)]
  exact valuation_eq_exp_neg_count_spanSingleton v α

theorem fracIdealUnits_ext_count {I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), count F v (I : FractionalIdeal (𝓞 F)⁰ F)
      = count F v (J : FractionalIdeal (𝓞 F)⁰ F)) : I = J := by
  refine Units.ext ?_
  rw [← finprod_heightOneSpectrum_factorization' (K := F) I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' (K := F) J.ne_zero]
  exact finprod_congr fun v => by rw [h v]

theorem ideleIdeal_principal (α : Fˣ) :
    ideleIdeal (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α)
      = toPrincipalIdeal (𝓞 F) F α := by
  refine fracIdealUnits_ext_count fun v => ?_
  rw [count_ideleIdeal, ordAt_unitAtHom_principal, coe_toPrincipalIdeal]

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_IdeleIdealClass2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_ArchLogEmbedding

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal IsDedekindDomain FractionalIdeal M4aHerbrand"

open scoped nonZeroDivisors

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

def integralUnitEmb : (𝓞 F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom).comp
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom)

theorem integralUnitEmb_mem_principalIdeles (u : (𝓞 F)ˣ) :
    integralUnitEmb u ∈ principalIdeles (𝓞 F) F :=
  ⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom u, rfl⟩

theorem principal_mem_unitsOutside_empty_iff (α : Fˣ) :
    (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α) ∈ unitsOutside (F := F) ∅
      ↔ toPrincipalIdeal (𝓞 F) F α = 1 := by
  rw [← ker_ideleIdeal, MonoidHom.mem_ker, ideleIdeal_principal]

theorem toPrincipalIdeal_eq_one_iff (α : Fˣ) :
    toPrincipalIdeal (𝓞 F) F α = 1
      ↔ α ∈ (Units.map (algebraMap (𝓞 F) F).toMonoidHom).range := by
  rw [← Units.val_eq_one, coe_toPrincipalIdeal, ← spanSingleton_one (S := (𝓞 F)⁰),
    spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    rw [Units.smul_def, Algebra.smul_def] at hz
    have hz0 : algebraMap (𝓞 F) F ↑z ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne (Units.ne_zero z)
    have h1 : algebraMap (𝓞 F) F ↑z * algebraMap (𝓞 F) F ↑z⁻¹ = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    exact ⟨z⁻¹, Units.ext (mul_left_cancel₀ hz0 (h1.trans hz.symm))⟩
  · rintro ⟨z, rfl⟩
    refine ⟨z⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def]
    show algebraMap (𝓞 F) F ↑z⁻¹ * algebraMap (𝓞 F) F ↑z = 1
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

theorem range_integralUnitEmb :
    (integralUnitEmb (F := F)).range
      = principalIdeles (𝓞 F) F ⊓ unitsOutside (F := F) ∅ := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨integralUnitEmb_mem_principalIdeles u, ?_⟩
    have h := (principal_mem_unitsOutside_empty_iff
      (Units.map (algebraMap (𝓞 F) F).toMonoidHom u)).mpr
      ((toPrincipalIdeal_eq_one_iff _).mpr ⟨u, rfl⟩)
    exact h
  · rintro ⟨⟨α, hα⟩, hU⟩
    have hα' : (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom) α = x := hα
    rw [← hα'] at hU
    have hU' := (principal_mem_unitsOutside_empty_iff α).mp hU
    obtain ⟨u, rfl⟩ := (toPrincipalIdeal_eq_one_iff α).mp hU'
    exact ⟨u, hα'⟩

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_ArchLogEmbedding
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_FujisakiC1

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal M4aHerbrand"

namespace M4aLocalCFT
namespace FujisakiC1

variable (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]

theorem principalIdeles_le_normOneIdeles :
    principalIdeles (𝓞 F) F ≤ normOneIdeles F := by
  rintro x ⟨a, rfl⟩
  exact NumberField.AdeleRing.distribHaarChar_algebraMap F a

end M4aLocalCFT.FujisakiC1
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_FujisakiC1
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_LocalGlobalModulus

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

section LG

variable (v : HeightOneSpectrum (𝓞 F))

def coordAt (x : AdeleRing (𝓞 F) F) : v.adicCompletion F := (x.2 : FiniteAdeleRing (𝓞 F) F) v

theorem continuous_coordAt : Continuous (coordAt (F := F) v) :=
  (continuous_finAdeleEval (𝓞 F) F v).comp (continuous_adeleFin (𝓞 F) F)

open scoped Classical in
def finSingle (c : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨Function.update 0 v c,
    Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
      by_contra hwv
      exact hw (by rw [Function.update_of_ne hwv]; exact zero_mem _))⟩

open scoped Classical in
theorem finSingle_apply_self (c : v.adicCompletion F) : (finSingle v c : FiniteAdeleRing (𝓞 F) F) v = c := by
  show Function.update (0 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v c v = c
  simp

open scoped Classical in
theorem finSingle_apply_of_ne (c : v.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (finSingle v c : FiniteAdeleRing (𝓞 F) F) w = 0 := by
  show Function.update (0 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v c w = 0
  simp [Function.update_of_ne hw]

def adeleSingle (c : v.adicCompletion F) : AdeleRing (𝓞 F) F := ((0 : InfiniteAdeleRing F), finSingle v c)

theorem coordAt_adeleSingle_add (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F) :
    coordAt v (adeleSingle v c + x) = c + coordAt v x := by
  show (finSingle v c : FiniteAdeleRing (𝓞 F) F) v + (x.2 : FiniteAdeleRing (𝓞 F) F) v = c + _
  rw [finSingle_apply_self]
  rfl

theorem adeleSingle_add_fst (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F) :
    (adeleSingle v c + x).1 = x.1 := by
  show (0 : InfiniteAdeleRing F) + x.1 = x.1
  rw [zero_add]

theorem adeleSingle_add_snd_apply_of_ne (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    ((adeleSingle v c + x).2 : FiniteAdeleRing (𝓞 F) F) w = (x.2 : FiniteAdeleRing (𝓞 F) F) w := by
  show (finSingle v c : FiniteAdeleRing (𝓞 F) F) w + (x.2 : FiniteAdeleRing (𝓞 F) F) w = _
  rw [finSingle_apply_of_ne v c hw, zero_add]

def slab (B : Set (InfiniteAdeleRing F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 ∈ B ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}

def box (B : Set (InfiniteAdeleRing F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 ∈ B ∧ ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}

theorem preimage_adeleSingle_add_slab (B : Set (InfiniteAdeleRing F)) (c : v.adicCompletion F) :
    (fun x => adeleSingle v c + x) ⁻¹' slab v B = slab v B := by
  ext x
  simp only [Set.mem_preimage, slab, Set.mem_setOf_eq, adeleSingle_add_fst]
  refine and_congr Iff.rfl (forall₂_congr fun w hw => ?_)
  rw [adeleSingle_add_snd_apply_of_ne v c x hw]

theorem preimage_adeleSingle_add_coordAt (c : v.adicCompletion F) (E : Set (v.adicCompletion F)) :
    (fun x => adeleSingle v c + x) ⁻¹' (coordAt v ⁻¹' E) = coordAt v ⁻¹' ((fun y => c + y) ⁻¹' E) := by
  ext x
  simp only [Set.mem_preimage, coordAt_adeleSingle_add]

theorem coordAt_preimage_integers_inter_slab (B : Set (InfiniteAdeleRing F)) :
    coordAt v ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∩ slab v B = box B := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, slab, box, Set.mem_setOf_eq, coordAt]
  constructor
  · rintro ⟨hv, hB, hw⟩
    refine ⟨hB, fun w => ?_⟩
    by_cases h : w = v
    · subst h; exact hv
    · exact hw w h
  · rintro ⟨hB, hw⟩
    exact ⟨hw v, hB, fun w _ => hw w⟩

theorem isCompact_box {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) : IsCompact (box (F := F) B) := by
  have h := hB.prod (isCompact_integralFiniteAdeles (𝓞 F) F)
  exact h

theorem isOpen_openBox (B : Set (InfiniteAdeleRing F)) :
    IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
      ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B} :=
    isOpen_interior.preimage (continuous_adeleArch (𝓞 F) F)
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

theorem isOpen_openSlab (B : Set (InfiniteAdeleRing F)) :
    IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B} :=
    isOpen_interior.preimage (continuous_adeleArch (𝓞 F) F)
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
    have h := RestrictedProduct.isOpen_forall_imp_mem
      (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      Fact.out (p := fun w => w ≠ v)
    exact h.preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

def slabPush (μ : Measure (AdeleRing (𝓞 F) F)) (B : Set (InfiniteAdeleRing F)) : Measure (v.adicCompletion F) :=
  Measure.map (coordAt v) (μ.restrict (slab v B))

theorem slabPush_apply (μ : Measure (AdeleRing (𝓞 F) F)) (B : Set (InfiniteAdeleRing F))
    {E : Set (v.adicCompletion F)} (hE : MeasurableSet E) :
    slabPush v μ B E = μ (coordAt v ⁻¹' E ∩ slab v B) := by
  rw [slabPush, Measure.map_apply (continuous_coordAt v).measurable hE,
    Measure.restrict_apply ((continuous_coordAt v).measurable hE)]

theorem isAddLeftInvariant_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : Set (InfiniteAdeleRing F)) : (slabPush v μ B).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun c E hE => ?_
  rw [slabPush_apply v μ B hE, slabPush_apply v μ B (measurable_const_add c hE),
    ← preimage_adeleSingle_add_coordAt v c E]
  conv_lhs => rw [← preimage_adeleSingle_add_slab v B c]
  rw [← Set.preimage_inter]
  exact measure_preimage_add μ (adeleSingle v c) _

theorem slabPush_integers_lt_top (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) :
    slabPush v μ B (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ := by
  rw [slabPush_apply v μ B (isClosed_adicCompletionIntegers v).measurableSet,
    coordAt_preimage_integers_inter_slab]
  exact (isCompact_box hB).measure_lt_top

theorem isFiniteMeasureOnCompacts_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) :
    IsFiniteMeasureOnCompacts (slabPush v μ B) := by
  haveI := isAddLeftInvariant_slabPush v μ B
  refine ⟨fun K hK => ?_⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := NumberField.isOpenAdicCompletionIntegers F v
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : v.adicCompletion F => c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun c => hO.vadd c)
    (fun c hc => Set.mem_iUnion.mpr ⟨c, Set.mem_vadd_set.mpr ⟨0, zero_mem _, by simp⟩⟩)
  calc slabPush v μ B K
      ≤ slabPush v μ B (⋃ c ∈ t, c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := measure_mono ht
    _ ≤ ∑ c ∈ t, slabPush v μ B (c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
        measure_biUnion_finset_le t _
    _ = ∑ _c ∈ t, slabPush v μ B (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact measure_vadd _ c _
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (slabPush_integers_lt_top v μ hB)

theorem isOpenPosMeasure_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsOpenPosMeasure μ]
    {B : Set (InfiniteAdeleRing F)} (hB : (interior B).Nonempty) : IsOpenPosMeasure (slabPush v μ B) := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨c, hc⟩ := hne
  obtain ⟨b, hb⟩ := hB
  rw [slabPush_apply v μ B hU.measurableSet]
  have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U ⊆ coordAt v ⁻¹' U ∩ slab v B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, interior_subset h1, h2⟩
  have hopen : IsOpen ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U) :=
    (isOpen_openSlab v B).inter (hU.preimage (continuous_coordAt v))
  have hne' : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U).Nonempty := by
    refine ⟨((b, finSingle v c) : AdeleRing (𝓞 F) F), ⟨hb, fun w hw => ?_⟩, ?_⟩
    · show (finSingle v c : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F
      rw [finSingle_apply_of_ne v c hw]
      exact zero_mem _
    · show (finSingle v c : FiniteAdeleRing (𝓞 F) F) v ∈ U
      rw [finSingle_apply_self]
      exact hc
  exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos μ hne') (measure_mono hsub))

end Measure
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

theorem embUnit_val_mul_fst (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 = x.1 := by
  show ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 * x.1 = x.1
  rw [embUnit_val_fst, one_mul]

theorem embUnit_val_mul_snd_apply_self (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) v
      = (t : v.adicCompletion F) * (x.2 : FiniteAdeleRing (𝓞 F) F) v := by
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
      * (x.2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [localUnit_apply_self]

theorem embUnit_val_mul_snd_apply_of_ne (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) w
      = (x.2 : FiniteAdeleRing (𝓞 F) F) w := by
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w
      * (x.2 : FiniteAdeleRing (𝓞 F) F) w = _
  rw [localUnit_apply_of_ne (𝓞 F) F v t hw, one_mul]

theorem embUnit_smul_box (t : (v.adicCompletion F)ˣ) (B : Set (InfiniteAdeleRing F)) :
    (embUnit v t) • box (F := F) B
      = coordAt v ⁻¹' ((t : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∩ slab v B := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxB, hxint⟩, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · show (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) v
        ∈ (t : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [embUnit_val_mul_snd_apply_self]
      exact Set.smul_mem_smul_set (hxint v)
    · show (((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 ∈ B
      rw [embUnit_val_mul_fst]; exact hxB
    · show (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) w
        ∈ w.adicCompletionIntegers F
      rw [embUnit_val_mul_snd_apply_of_ne v t x hw]; exact hxint w
  · rintro ⟨hv, hB, hw⟩
    obtain ⟨z, hz, hvz⟩ := Set.mem_smul_set.mp hv
    refine ⟨(embUnit v t⁻¹) • y, ⟨?_, fun w => ?_⟩, ?_⟩
    · show (((embUnit v t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 ∈ B
      rw [embUnit_val_mul_fst]; exact hB
    · by_cases hwv : w = v
      · subst hwv
        show (((((embUnit w t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 : FiniteAdeleRing (𝓞 F) F)) w
          ∈ w.adicCompletionIntegers F
        rw [embUnit_val_mul_snd_apply_self]
        have hyv : (y.2 : FiniteAdeleRing (𝓞 F) F) w = (t : w.adicCompletion F) * z := by
          show coordAt w y = (t : w.adicCompletion F) * z
          rw [← hvz]; rfl
        rw [hyv, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · show (((((embUnit v t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 : FiniteAdeleRing (𝓞 F) F)) w
          ∈ w.adicCompletionIntegers F
        rw [embUnit_val_mul_snd_apply_of_ne v t⁻¹ y hwv]; exact hw w hwv
    · show (embUnit v t) • ((embUnit v t⁻¹) • y) = y
      rw [map_inv, smul_inv_smul]

theorem distribHaarChar_embUnit (t : (v.adicCompletion F)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (embUnit v t)
      = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-(ordAt v t)) := by
  borelize (AdeleRing (𝓞 F) F)
  borelize (v.adicCompletion F)
  obtain ⟨B⟩ : Nonempty (PositiveCompacts (InfiniteAdeleRing F)) := inferInstance
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  have hBc : IsCompact (B : Set (InfiniteAdeleRing F)) := B.isCompact
  have hBi : (interior (B : Set (InfiniteAdeleRing F))).Nonempty := B.interior_nonempty
  have hs_top : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ ∞ := (isCompact_box hBc).measure_lt_top.ne
  have hs0 : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ 0 := by
    obtain ⟨b, hb⟩ := hBi
    have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
        ⊆ box (F := F) (B : Set (InfiniteAdeleRing F)) := fun x hx => ⟨interior_subset hx.1, hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), hb, fun w => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openBox (F := F) _).measure_pos μ hne) (measure_mono hsub))
  haveI := isAddLeftInvariant_slabPush v μ (B : Set (InfiniteAdeleRing F))
  haveI := isFiniteMeasureOnCompacts_slabPush v μ hBc
  haveI := isOpenPosMeasure_slabPush v μ hBi
  haveI : (slabPush v μ (B : Set (InfiniteAdeleRing F))).IsAddHaarMeasure := {}
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := NumberField.isOpenAdicCompletionIntegers F v
  haveI : (slabPush v μ (B : Set (InfiniteAdeleRing F))).Regular :=
    Measure.regular_of_isAddLeftInvariant (NumberField.isCompactAdicCompletionIntegers F v)
      (by rw [hO.interior_eq]; exact ⟨0, zero_mem _⟩) (slabPush_integers_lt_top v μ hBc).ne
  have hlam := M4aLocalCFT.LocalHaarModulus.measure_smul_integers (slabPush v μ (B : Set (InfiniteAdeleRing F))) t
  rw [slabPush_apply v μ _ ((hO.smul₀ t.ne_zero).measurableSet),
    slabPush_apply v μ _ (isClosed_adicCompletionIntegers v).measurableSet,
    coordAt_preimage_integers_inter_slab] at hlam
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [embUnit_smul_box]
  exact hlam

theorem distribHaarChar_embUnit_eq_local (t : (v.adicCompletion F)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (embUnit v t) = distribHaarChar (v.adicCompletion F) t := by
  rw [distribHaarChar_embUnit, M4aLocalCFT.LocalHaarModulus.distribHaarChar_adicCompletion]
  rfl

theorem distribHaarChar_eq_one_of_integral {g : (AdeleRing (𝓞 F) F)ˣ} (h1 : ((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1)
    (hint : ∀ w : HeightOneSpectrum (𝓞 F), ((g : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F)
    (hint' : ∀ w : HeightOneSpectrum (𝓞 F), (((g⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w
      ∈ w.adicCompletionIntegers F) :
    distribHaarChar (AdeleRing (𝓞 F) F) g = 1 := by
  borelize (AdeleRing (𝓞 F) F)
  obtain ⟨B⟩ : Nonempty (PositiveCompacts (InfiniteAdeleRing F)) := inferInstance
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  have hBc : IsCompact (B : Set (InfiniteAdeleRing F)) := B.isCompact
  have hs_top : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ ∞ := (isCompact_box hBc).measure_lt_top.ne
  have hs0 : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ 0 := by
    obtain ⟨b, hb⟩ := B.interior_nonempty
    have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
        ⊆ box (F := F) (B : Set (InfiniteAdeleRing F)) := fun x hx => ⟨interior_subset hx.1, hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), hb, fun w => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openBox (F := F) _).measure_pos μ hne) (measure_mono hsub))
  have h1' : (((g⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 = 1 := inv_val_fst_eq_one g h1
  have hfix : ∀ (k : (AdeleRing (𝓞 F) F)ˣ), ((k : AdeleRing (𝓞 F) F).1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((k : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F) →
      ∀ x ∈ box (F := F) (B : Set (InfiniteAdeleRing F)), k • x ∈ box (F := F) (B : Set (InfiniteAdeleRing F)) := by
    intro k hk1 hkint x hx
    refine ⟨?_, fun w => ?_⟩
    · show ((k : AdeleRing (𝓞 F) F).1 * x.1) ∈ (B : Set (InfiniteAdeleRing F))
      rw [hk1, one_mul]; exact hx.1
    · show ((k : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w * (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ _
      exact mul_mem (hkint w) (hx.2 w)
  have hset : g • box (F := F) (B : Set (InfiniteAdeleRing F)) = box (F := F) (B : Set (InfiniteAdeleRing F)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hfix g h1 hint x hx
    · intro hy
      exact ⟨g⁻¹ • y, hfix g⁻¹ h1' hint' y hy, smul_inv_smul g y⟩
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [hset, ENNReal.coe_one, one_mul]

end LG
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end Fold_LocalGlobalModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

section Fold_TateAssembly

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.AdelicLevel IsDedekindDomain Topology TopologicalSpace Set"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

scoped instance instSecondCountableCompletion (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

section Assembly

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev DeepUnits : Type := (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) → (v.1.adicCompletionIntegers F)ˣ

abbrev SUnits : Type := (v : S) → (v.1.adicCompletion F)ˣ

scoped instance instCompactSpaceDeepUnits : CompactSpace (DeepUnits (F := F) S) := by infer_instance

open scoped Classical in
def extendUnits : DeepUnits (F := F) S →* ((v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ) where
  toFun o v := if h : v ∈ S then 1 else o ⟨v, h⟩
  map_one' := by
    funext v
    by_cases h : v ∈ S
    · rw [dif_pos h]; rfl
    · rw [dif_neg h]; rfl
  map_mul' o o' := by
    funext v
    by_cases h : v ∈ S
    · rw [Pi.mul_apply, dif_pos h, dif_pos h, dif_pos h, one_mul]
    · rw [Pi.mul_apply, dif_neg h, dif_neg h, dif_neg h]; rfl

open scoped Classical in
theorem extendUnits_apply_of_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    extendUnits S o v = 1 := by
  show (if h : v ∈ S then (1 : (v.adicCompletionIntegers F)ˣ) else o ⟨v, h⟩) = 1
  rw [dif_pos hv]

open scoped Classical in
theorem extendUnits_apply_of_not_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    extendUnits S o v = o ⟨v, hv⟩ := by
  show (if h : v ∈ S then (1 : (v.adicCompletionIntegers F)ˣ) else o ⟨v, h⟩) = o ⟨v, hv⟩
  rw [dif_neg hv]

theorem continuous_extendUnits : Continuous (extendUnits (F := F) S) := by
  refine continuous_pi fun v => ?_
  by_cases h : v ∈ S
  · have : (fun o : DeepUnits (F := F) S => extendUnits S o v) = fun _ => 1 := by
      funext o; exact extendUnits_apply_of_mem S o h
    rw [this]; exact continuous_const
  · have : (fun o : DeepUnits (F := F) S => extendUnits S o v) = fun o => o ⟨v, h⟩ := by
      funext o; exact extendUnits_apply_of_not_mem S o h
    rw [this]; exact continuous_apply _

def structureRingHom : ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun x := RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x
  map_one' := RestrictedProduct.ext _ _ fun _ => rfl
  map_mul' _ _ := RestrictedProduct.ext _ _ fun _ => rfl
  map_zero' := RestrictedProduct.ext _ _ fun _ => rfl
  map_add' _ _ := RestrictedProduct.ext _ _ fun _ => rfl

theorem continuous_structureRingHom : Continuous (structureRingHom (F := F)) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

def piUnitsInv : ((v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ)
    →* ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F)ˣ :=
  MulEquiv.piUnits.symm.toMonoidHom

theorem continuous_piUnitsInv : Continuous (piUnitsInv (F := F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)
  · exact continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)

def deepAsm : DeepUnits (F := F) S →* (AdeleRing (𝓞 F) F)ˣ :=
  ((Units.map ((finIncl (𝓞 F) F).comp (structureRingHom (F := F)).toMonoidHom)).comp piUnitsInv).comp (extendUnits S)

theorem continuous_deepAsm : Continuous (deepAsm (F := F) S) :=
  ((Units.continuous_map ((continuous_const.prodMk continuous_id : Continuous fun x : FiniteAdeleRing (𝓞 F) F =>
      (((1 : InfiniteAdeleRing F), x) : AdeleRing (𝓞 F) F)).comp continuous_structureRingHom)).comp
    continuous_piUnitsInv).comp (continuous_extendUnits S)

theorem deepAsm_val_fst (o : DeepUnits (F := F) S) : ((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 :=
  rfl

theorem deepAsm_val_snd_apply (o : DeepUnits (F := F) S) (v : HeightOneSpectrum (𝓞 F)) :
    (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((extendUnits S o v : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :=
  rfl

theorem unitAtHom_deepAsm_of_not_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (deepAsm S o) = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (o ⟨v, hv⟩) := by
  refine Units.ext ?_
  show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [deepAsm_val_snd_apply, extendUnits_apply_of_not_mem S o hv]
  rfl

theorem unitAtHom_deepAsm_of_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (deepAsm S o) = 1 := by
  refine Units.ext ?_
  show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [deepAsm_val_snd_apply, extendUnits_apply_of_mem S o hv]
  rfl

theorem deepAsm_mem_unitsOutside (o : DeepUnits (F := F) S) : deepAsm S o ∈ unitsOutside S := by
  rw [mem_unitsOutside_iff]
  constructor
  · intro v hv
    show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    rw [deepAsm_val_snd_apply]
    exact SetLike.coe_mem _
  · intro v hv
    rw [← map_inv]
    show (((deepAsm S o⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    rw [deepAsm_val_snd_apply]
    exact SetLike.coe_mem _

end Assembly
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_TateAssembly
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_ArchLocalGlobalModulus

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.AdelicLevel NumberField.AdelicVolume IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

section LGArch

variable (w : InfinitePlace F)

def archCoord (x : AdeleRing (𝓞 F) F) : w.Completion := x.1 w

theorem continuous_archCoord : Continuous (archCoord (F := F) w) := by
  show Continuous fun x : AdeleRing (𝓞 F) F => (fun y : InfiniteAdeleRing F => y w) (adeleArch (𝓞 F) F x)
  exact (continuous_apply w).comp (continuous_adeleArch (𝓞 F) F)

open scoped Classical in
def archSingle (c : w.Completion) : AdeleRing (𝓞 F) F :=
  ((Function.update (0 : InfiniteAdeleRing F) w c), (0 : FiniteAdeleRing (𝓞 F) F))

open scoped Classical in
theorem archCoord_archSingle_add (c : w.Completion) (x : AdeleRing (𝓞 F) F) :
    archCoord w (archSingle w c + x) = c + archCoord w x := by
  show Function.update (0 : InfiniteAdeleRing F) w c w + x.1 w = c + x.1 w
  rw [Function.update_self]

open scoped Classical in
theorem archSingle_add_fst_of_ne (c : w.Completion) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) : (archSingle w c + x).1 w' = x.1 w' := by
  show Function.update (0 : InfiniteAdeleRing F) w c w' + x.1 w' = x.1 w'
  rw [Function.update_of_ne hw]
  exact zero_add _

theorem archSingle_add_snd (c : w.Completion) (x : AdeleRing (𝓞 F) F) : (archSingle w c + x).2 = x.2 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) + x.2 = x.2
  exact zero_add _

def archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  {x | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ B w') ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

def archBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  box (F := F) (Set.pi Set.univ B)

theorem mem_archBox_iff (B : (w' : InfinitePlace F) → Set (w'.Completion)) (x : AdeleRing (𝓞 F) F) :
    x ∈ archBox B ↔ (∀ w' : InfinitePlace F, x.1 w' ∈ B w') ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' => h1 w' (Set.mem_univ _), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' _ => h1 w', h2⟩

theorem preimage_archSingle_add_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) (c : w.Completion) :
    (fun x => archSingle w c + x) ⁻¹' archSlab w B = archSlab w B := by
  ext x
  simp only [Set.mem_preimage, archSlab, Set.mem_setOf_eq, archSingle_add_snd]
  refine and_congr (forall₂_congr fun w' hw => ?_) Iff.rfl
  rw [archSingle_add_fst_of_ne w c x hw]

theorem preimage_archSingle_add_archCoord (c : w.Completion) (E : Set (w.Completion)) :
    (fun x => archSingle w c + x) ⁻¹' (archCoord w ⁻¹' E) = archCoord w ⁻¹' ((fun y => c + y) ⁻¹' E) := by
  ext x
  simp only [Set.mem_preimage, archCoord_archSingle_add]

theorem archCoord_preimage_inter_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    archCoord w ⁻¹' (B w) ∩ archSlab w B = archBox B := by
  ext x
  rw [mem_archBox_iff]
  simp only [Set.mem_inter_iff, Set.mem_preimage, archSlab, Set.mem_setOf_eq, archCoord]
  constructor
  · rintro ⟨hw, hB, hv⟩
    refine ⟨fun w' => ?_, hv⟩
    by_cases h : w' = w
    · subst h; exact hw
    · exact hB w' h
  · rintro ⟨hB, hv⟩
    exact ⟨hB w, fun w' _ => hB w', hv⟩

theorem isCompact_archBox {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    IsCompact (archBox (F := F) B) :=
  isCompact_box (isCompact_univ_pi hB)

theorem isOpen_openArchSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, ⋂ (_ : w' ≠ w), archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_iInter_of_finite fun _ =>
      isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

theorem isOpen_openArchBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (w.Completion)] [BorelSpace (w.Completion)]

def archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    Measure (w.Completion) :=
  Measure.map (archCoord w) (μ.restrict (archSlab w B))

theorem archSlabPush_apply (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion))
    {E : Set (w.Completion)} (hE : MeasurableSet E) :
    archSlabPush w μ B E = μ (archCoord w ⁻¹' E ∩ archSlab w B) := by
  rw [archSlabPush, Measure.map_apply (continuous_archCoord w).measurable hE,
    Measure.restrict_apply ((continuous_archCoord w).measurable hE)]

theorem isAddLeftInvariant_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : (w' : InfinitePlace F) → Set (w'.Completion)) : (archSlabPush w μ B).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun c E hE => ?_
  rw [archSlabPush_apply w μ B hE, archSlabPush_apply w μ B (measurable_const_add c hE),
    ← preimage_archSingle_add_archCoord w c E]
  conv_lhs => rw [← preimage_archSingle_add_archSlab w B c]
  rw [← Set.preimage_inter]
  exact measure_preimage_add μ (archSingle w c) _

theorem archSlabPush_self_lt_top (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    archSlabPush w μ B (B w) < ∞ := by
  rw [archSlabPush_apply w μ B (hB w).measurableSet, archCoord_preimage_inter_archSlab]
  exact (isCompact_archBox hB).measure_lt_top

theorem isFiniteMeasureOnCompacts_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w'))
    (hBi : (interior (B w)).Nonempty) :
    IsFiniteMeasureOnCompacts (archSlabPush w μ B) := by
  haveI := isAddLeftInvariant_archSlabPush w μ B
  obtain ⟨b₀, hb₀⟩ := hBi
  refine ⟨fun K hK => ?_⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : w.Completion => (c - b₀) +ᵥ interior (B w))
    (fun c => isOpen_interior.vadd (c - b₀))
    (fun c _ => Set.mem_iUnion.mpr ⟨c, Set.mem_vadd_set.mpr ⟨b₀, hb₀, by simp⟩⟩)
  calc archSlabPush w μ B K
      ≤ archSlabPush w μ B (⋃ c ∈ t, (c - b₀) +ᵥ interior (B w)) := measure_mono ht
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ interior (B w)) := measure_biUnion_finset_le t _
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ B w) :=
        Finset.sum_le_sum fun c _ => measure_mono (Set.vadd_set_mono interior_subset)
    _ = ∑ _c ∈ t, archSlabPush w μ B (B w) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact measure_vadd _ (c - b₀) _
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (archSlabPush_self_lt_top w μ hB)

theorem isOpenPosMeasure_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsOpenPosMeasure μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hBi : ∀ w', (interior (B w')).Nonempty) :
    IsOpenPosMeasure (archSlabPush w μ B) := by
  classical
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨c, hc⟩ := hne
  choose b hb using hBi
  rw [archSlabPush_apply w μ B hU.measurableSet]
  have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U ⊆ archCoord w ⁻¹' U ∩ archSlab w B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, fun w' hw => interior_subset (h1 w' hw), h2⟩
  have hopen := (isOpen_openArchSlab w B).inter (hU.preimage (continuous_archCoord w))
  have hne' : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U).Nonempty := by
    refine ⟨((Function.update b w c, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F),
      ⟨fun w' hw => ?_, fun v => zero_mem _⟩, ?_⟩
    · show Function.update b w c w' ∈ interior (B w')
      rw [Function.update_of_ne hw]
      exact hb w'
    · show Function.update b w c w ∈ U
      rw [Function.update_self]
      exact hc
  exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos μ hne') (measure_mono hsub))

end Measure
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

theorem archCentralUnit_val_mul_fst_self (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w = (a : w.Completion) * x.1 w := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * x.1 w = _
  rw [archCentralUnit_fst_self]

theorem archCentralUnit_val_mul_fst_of_ne (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' = x.1 w' := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w' * x.1 w' = _
  rw [archCentralUnit_fst_of_ne w a hw, one_mul]

theorem archCentralUnit_val_mul_snd (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 = x.2 := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * x.2 = _
  rw [archCentralUnit_snd, one_mul]

theorem archCentralUnit_smul_archBox (a : (w.Completion)ˣ) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    (archCentralUnit F w a) • archBox (F := F) B = archCoord w ⁻¹' (a • B w) ∩ archSlab w B := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_archBox_iff] at hy
    obtain ⟨hB, hv⟩ := hy
    refine ⟨?_, fun w' hw => ?_, fun v => ?_⟩
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w ∈ a • B w
      rw [archCentralUnit_val_mul_fst_self]
      exact Set.smul_mem_smul_set (hB w)
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w' ∈ B w'
      rw [archCentralUnit_val_mul_fst_of_ne w a y hw]
      exact hB w'
    · show ((((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 :
          FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      rw [archCentralUnit_val_mul_snd]
      exact hv v
  · rintro ⟨hw, hB, hv⟩
    refine ⟨(archUnitHom w a⁻¹) • x, ?_, ?_⟩
    · rw [mem_archBox_iff]
      refine ⟨fun w' => ?_, fun v => ?_⟩
      · by_cases h : w' = w
        · subst h
          show (((archCentralUnit F w' a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_self]
          obtain ⟨b, hb, hbx⟩ := Set.mem_smul_set.mp hw
          have : x.1 w' = (a : w'.Completion) * b := hbx.symm
          rw [this, ← mul_assoc, Units.inv_mul, one_mul]
          exact hb
        · show (((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_of_ne w a⁻¹ x h]
          exact hB w' h
      · show ((((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 :
            FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
        rw [archCentralUnit_val_mul_snd]
        exact hv v
    · show (archUnitHom w a) • ((archUnitHom w a⁻¹) • x) = x
      rw [map_inv, smul_inv_smul]

theorem distribHaarChar_archCentralUnit (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archCentralUnit F w a) = distribHaarChar (w.Completion) a := by
  borelize (AdeleRing (𝓞 F) F)
  borelize (w.Completion)
  set B : (w' : InfinitePlace F) → PositiveCompacts (w'.Completion) := fun w' => Classical.arbitrary _ with hBdef
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  set Bs : (w' : InfinitePlace F) → Set (w'.Completion) := fun w' => (B w' : Set (w'.Completion)) with hBs
  have hBc : ∀ w', IsCompact (Bs w') := fun w' => (B w').isCompact
  have hBi : ∀ w', (interior (Bs w')).Nonempty := fun w' => (B w').interior_nonempty
  have hs_top : μ (archBox (F := F) Bs) ≠ ∞ := (isCompact_archBox hBc).measure_lt_top.ne
  have hs0 : μ (archBox (F := F) Bs) ≠ 0 := by
    classical
    choose b hb using hBi
    have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
        ⊆ archBox (F := F) Bs := by
      intro x hx
      rw [mem_archBox_iff]
      exact ⟨fun w' => interior_subset (hx.1 w'), hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), fun w' => hb w', fun v => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openArchBox (F := F) Bs).measure_pos μ hne) (measure_mono hsub))
  haveI := isAddLeftInvariant_archSlabPush w μ Bs
  haveI := isFiniteMeasureOnCompacts_archSlabPush w μ hBc (hBi w)
  haveI := isOpenPosMeasure_archSlabPush w μ hBi
  haveI : (archSlabPush w μ Bs).IsAddHaarMeasure := {}
  haveI : (archSlabPush w μ Bs).Regular :=
    Measure.regular_of_isAddLeftInvariant (hBc w) (hBi w) (archSlabPush_self_lt_top w μ hBc).ne
  have key := distribHaarChar_mul (archSlabPush w μ Bs) a (Bs w)
  rw [archSlabPush_apply w μ Bs ((hBc w).smul (a : (w.Completion)ˣ)).measurableSet,
    archSlabPush_apply w μ Bs (hBc w).measurableSet, archCoord_preimage_inter_archSlab] at key
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [archCentralUnit_smul_archBox]
  exact key.symm

theorem distribHaarChar_archUnitHom (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archUnitHom w a) = distribHaarChar (w.Completion) a :=
  distribHaarChar_archCentralUnit w a

end LGArch
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_ArchLocalGlobalModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_ArchMulHaarReal

set_option autoImplicit false

open MeasureTheory Set Filter Topology

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarReal

variable (μ : Measure ℝ) [μ.IsAddHaarMeasure]

theorem distribHaarChar_real (t : ℝˣ) : distribHaarChar ℝ t = ‖(t : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := Icc (0 : ℝ) 1)
    (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc]) ?_
  have hset : t • Icc (0 : ℝ) 1 = (t : ℝ) • Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, Measure.addHaar_smul volume (t : ℝ) (Icc (0 : ℝ) 1),
    Module.finrank_self, pow_one, Real.volume_Icc]
  rw [← Real.norm_eq_abs, ofReal_norm]
  rfl

variable [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]

end ArchMulHaarReal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_ArchMulHaarReal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_ArchMulHaarComplex

set_option autoImplicit false

open MeasureTheory Set

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarComplex

theorem det_lmul_complex (c : ℂ) :
    LinearMap.det (Algebra.lmul ℝ ℂ c) = Complex.normSq c := by
  have hap : ∀ x : ℂ, (Algebra.lmul ℝ ℂ c) x = c * x := fun _ => rfl
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, hap]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

theorem smul_set_eq_image_lmul (c : ℂ) (s : Set ℂ) :
    c • s = (Algebra.lmul ℝ ℂ c) '' s := by
  ext x
  simp [Set.mem_smul_set]

theorem measure_smul_complex (μ : Measure ℂ) [μ.IsAddHaarMeasure] (c : ℂ)
    (s : Set ℂ) :
    μ (c • s) = (‖c‖₊ ^ 2 : ℝ≥0∞) * μ s := by
  rw [smul_set_eq_image_lmul, Measure.addHaar_image_linearMap μ _ s, det_lmul_complex]
  congr 1
  rw [abs_of_nonneg (Complex.normSq_nonneg c), ← Complex.norm_mul_self_eq_normSq,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, sq]
  rfl

theorem distribHaarChar_complex (t : ℂˣ) : distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Metric.ball (0 : ℂ) 1)
    (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos)) measure_ball_lt_top.ne ?_
  have hset : t • Metric.ball (0 : ℂ) 1 = ((t : ℂ)) • Metric.ball (0 : ℂ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, measure_smul_complex volume (t : ℂ)]
  norm_cast

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]

end ArchMulHaarComplex
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_ArchMulHaarComplex
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_ArchMulHaarCompletion

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarCompletion

theorem distribHaarChar_eq_of_ringEquiv {K L : Type} [Field K] [Field L]
    [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace L] [IsTopologicalRing L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L]
    (Φ : K ≃+* L) (hΦ : Continuous Φ) (hΦs : Continuous Φ.symm)
    (μL : Measure L) [μL.IsAddHaarMeasure] [μL.Regular]
    {B : Set L} (hB : MeasurableSet B) (hB0 : μL B ≠ 0) (hBt : μL B ≠ ∞)
    (t : Kˣ) :
    distribHaarChar K t = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) := by
  set e : L ≃+ K := Φ.symm.toAddEquiv with he
  have hecont : Continuous e := hΦs
  have hescont : Continuous e.symm := hΦ
  letI μK : Measure K := μL.map e
  haveI : μK.IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μL e hecont hescont
  haveI : μK.Regular :=
    Measure.Regular.map (⟨e.toEquiv, hecont, hescont⟩ : L ≃ₜ K)
  have key : ∀ (S : Set L), MeasurableSet S → μK (⇑Φ ⁻¹' S) = μL S := by
    intro S hS
    have hpre : ⇑e ⁻¹' (⇑Φ ⁻¹' S) = S := by
      ext x
      simp only [Set.mem_preimage, he]
      rw [show (Φ.symm.toAddEquiv x : K) = Φ.symm x from rfl, RingEquiv.apply_symm_apply]
    rw [show μK = μL.map e from rfl,
      Measure.map_apply hecont.measurable (hΦ.measurable hS), hpre]
  have hsmeas : MeasurableSet (⇑Φ ⁻¹' B) := hΦ.measurable hB
  have hs0 : μK (⇑Φ ⁻¹' B) ≠ 0 := by rw [key B hB]; exact hB0
  have hst : μK (⇑Φ ⁻¹' B) ≠ ∞ := by rw [key B hB]; exact hBt
  have hcomm : ∀ (u : Kˣ) (y : K),
      Φ ((u : K) * y) = ((Units.map (Φ : K →+* L).toMonoidHom u : Lˣ) : L) * Φ y := by
    intro u y
    rw [map_mul]
    rfl
  have hts : (t • (⇑Φ ⁻¹' B) : Set K)
      = ⇑Φ ⁻¹' ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Set.mem_preimage.mpr ?_
      have hfwd : Φ (t • y) = (Units.map (Φ : K →+* L).toMonoidHom t) • Φ y := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul]
        exact hcomm t y
      show Φ (t • y) ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B
      rw [hfwd]
      exact Set.smul_mem_smul_set hy
    · intro hx
      have hx' : Φ x ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B := Set.mem_preimage.mp hx
      refine ⟨(t⁻¹ : Kˣ) • x, Set.mem_preimage.mpr ?_, smul_inv_smul t x⟩
      have hbwd : Φ ((t⁻¹ : Kˣ) • x)
          = ((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) • Φ x := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcomm t⁻¹ x, map_inv]
      rw [hbwd]
      exact Set.mem_smul_set_iff_inv_smul_mem.mp hx'
  have hmul : μK (t • (⇑Φ ⁻¹' B))
      = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) * μK (⇑Φ ⁻¹' B) := by
    have hBs : MeasurableSet ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
      have : ((Units.map (Φ : K →+* L).toMonoidHom t) • B : Set L)
          = (fun y => (((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) : L) * y) ⁻¹' B := by
        ext y
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        rfl
      rw [this]
      exact hB.preimage (measurable_const_mul _)
    rw [hts, key _ hBs, key B hB, ← distribHaarChar_mul (μ := μL)]
  exact distribHaarChar_eq_of_measure_smul_eq_mul hs0 hst hmul

variable {F : Type} [Field F]

theorem nnnorm_ringEquivReal {w : InfinitePlace F} (hv : w.IsReal)
    (x : w.Completion) : ‖ringEquivRealOfIsReal hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) x

theorem nnnorm_ringEquivComplex {w : InfinitePlace F} (hv : w.IsComplex)
    (x : w.Completion) : ‖ringEquivComplexOfIsComplex hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

variable (w : InfinitePlace F) [MeasurableSpace w.Completion] [BorelSpace w.Completion]

theorem distribHaarChar_completion_of_isReal (hv : w.IsReal) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 1 := by
  have hiso := isometry_extensionEmbeddingOfIsReal hv
  have hcont : Continuous (ringEquivRealOfIsReal hv) := hiso.continuous
  have hconts : Continuous (ringEquivRealOfIsReal hv).symm := by
    have : Isometry (isometryEquivRealOfIsReal hv).symm := (isometryEquivRealOfIsReal hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivRealOfIsReal hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarReal.distribHaarChar_real, pow_one]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact nnnorm_ringEquivReal hv _

theorem distribHaarChar_completion_of_isComplex (hv : w.IsComplex) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 2 := by
  have hcont : Continuous (ringEquivComplexOfIsComplex hv) := (isometry_extensionEmbedding w).continuous
  have hconts : Continuous (ringEquivComplexOfIsComplex hv).symm := by
    have : Isometry (isometryEquivComplexOfIsComplex hv).symm :=
      (isometryEquivComplexOfIsComplex hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivComplexOfIsComplex hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarComplex.distribHaarChar_complex]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact congrArg (fun a => a ^ 2) (nnnorm_ringEquivComplex hv _)

variable {μ : Measure w.Completion} [μ.IsAddHaarMeasure] [μ.Regular]

variable [MeasurableSpace (w.Completion)ˣ] [BorelSpace (w.Completion)ˣ]

end ArchMulHaarCompletion
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_ArchMulHaarCompletion
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_FujisakiC3

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion M4aHerbrand P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable (F : Type) [Field F] [NumberField F]

theorem ideleNorm_archCentralUnit (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (NumberField.AdelicVolume.archCentralUnit F w a) =
      ((distribHaarChar (w.Completion) a : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [distribHaarChar_archCentralUnit]

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_FujisakiC3b

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion M4aHerbrand P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem distribHaarChar_completion_eq_pow_mult (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ w.mult := by
  rcases isReal_or_isComplex w with hv | hv
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isReal w hv, mult_isReal ⟨w, hv⟩]
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isComplex w hv, mult_isComplex ⟨w, hv⟩]

theorem ideleNorm_archUnitHom (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  borelize (w.Completion)
  rw [archUnitHom_apply, ideleNorm_archCentralUnit, distribHaarChar_completion_eq_pow_mult]
  push_cast
  rfl

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_FujisakiC3b
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_TateAssembly2

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.AdelicLevel IsDedekindDomain Topology TopologicalSpace Set Filter"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem idele_ext {x y : (AdeleRing (𝓞 F) F)ˣ} (harch : archUnits x = archUnits y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), unitAtHom v x = unitAtHom v y) : x = y := by
  refine Units.ext (Prod.ext ?_ ?_)
  · exact congrArg Units.val harch
  · refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    exact congrArg Units.val (hfin v)

section EmbUnitContinuity

variable (v : HeightOneSpectrum (𝓞 F))

omit [NumberField F] in
theorem cofinite_le_principal_compl_singleton :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite

open scoped Classical in
def finSinglePrincipal (c : v.adicCompletion F) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) :=
  ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c,
    Filter.eventually_principal.mpr fun w hw => by
      have hwv : w ≠ v := by simpa using hw
      show Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w ∈ _
      rw [Function.update_of_ne hwv]
      exact one_mem _⟩

open scoped Classical in
theorem continuous_finSinglePrincipal : Continuous (finSinglePrincipal (F := F) v) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun c : v.adicCompletion F =>
    Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w
  by_cases hw : w = v
  · subst hw
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hw]
    exact continuous_const

open scoped Classical in
theorem localUnit_val_eq (t : (v.adicCompletion F)ˣ) :
    ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v) (finSinglePrincipal v (t : v.adicCompletion F)) :=
  RestrictedProduct.ext (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) fun _ => rfl

theorem continuous_localUnit_val :
    Continuous fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
  have h : (fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
      = (RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v)) ∘ (finSinglePrincipal v) ∘ Units.val :=
    funext fun t => localUnit_val_eq v t
  rw [h]
  exact (RestrictedProduct.continuous_inclusion _).comp
    ((continuous_finSinglePrincipal v).comp Units.continuous_val)

theorem continuous_embUnit : Continuous (embUnit (F := F) v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)
  · have h : (fun t : (v.adicCompletion F)ˣ => (((embUnit v t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        = (fun t : (v.adicCompletion F)ˣ => ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ∘
            (fun t => t⁻¹) := by
      funext t
      simp only [Function.comp_apply, map_inv]
    rw [h]
    refine Continuous.comp ?_ continuous_inv
    show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)

end EmbUnitContinuity
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Assembly2

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem mem_unitsOutside_of_unitAtHom {x : (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ v ∉ S, (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    x ∈ unitsOutside S := by
  rw [mem_unitsOutside_iff]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · show (unitAtHom v x : v.adicCompletion F) ∈ _
    exact (h v hv).1
  · show (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ _
    exact (h v hv).2

theorem mem_unitsOutside_of_unitAtHom_eq_one {x : (AdeleRing (𝓞 F) F)ˣ} (h : ∀ v ∉ S, unitAtHom v x = 1) :
    x ∈ unitsOutside S := by
  refine mem_unitsOutside_of_unitAtHom S fun v hv => ?_
  rw [h v hv, inv_one, Units.val_one]
  exact ⟨one_mem _, one_mem _⟩

def archAsm : (InfiniteAdeleRing F)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun a :=
    { val := ((a : InfiniteAdeleRing F), 1)
      inv := (((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F), 1)
      val_inv := Prod.ext a.mul_inv (one_mul 1)
      inv_val := Prod.ext a.inv_mul (one_mul 1) }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext (Prod.ext rfl (one_mul 1).symm)

theorem archUnits_archAsm (a : (InfiniteAdeleRing F)ˣ) : archUnits (archAsm (F := F) a) = a := Units.ext rfl

theorem unitAtHom_archAsm (a : (InfiniteAdeleRing F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtHom v (archAsm (F := F) a) = 1 :=
  Units.ext rfl

theorem continuous_archAsm : Continuous (archAsm (F := F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun a : (InfiniteAdeleRing F)ˣ => (((a : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F)
    exact Units.continuous_val.prodMk continuous_const
  · show Continuous fun a : (InfiniteAdeleRing F)ˣ =>
      ((((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F)
    exact Units.continuous_coe_inv.prodMk continuous_const

theorem archAsm_mem_unitsOutside (a : (InfiniteAdeleRing F)ˣ) : archAsm (F := F) a ∈ unitsOutside S :=
  mem_unitsOutside_of_unitAtHom_eq_one S fun v _ => unitAtHom_archAsm a v

def sAsm : SUnits (F := F) S →* (AdeleRing (𝓞 F) F)ˣ where
  toFun t := ∏ v : S, embUnit v.1 (t v)
  map_one' := by simp only [Pi.one_apply, map_one, Finset.prod_const_one]
  map_mul' t t' := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

theorem sAsm_apply (t : SUnits (F := F) S) : sAsm S t = ∏ v : S, embUnit v.1 (t v) := rfl

theorem continuous_sAsm : Continuous (sAsm (F := F) S) := by
  show Continuous fun t : SUnits (F := F) S => ∏ v : S, embUnit v.1 (t v)
  exact continuous_finsetProd _ fun v _ => (continuous_embUnit v.1).comp (continuous_apply v)

theorem archUnits_sAsm (t : SUnits (F := F) S) : archUnits (sAsm S t) = 1 := by
  rw [sAsm_apply, map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  exact Units.ext (embUnit_val_fst v.1 (t v))

theorem unitAtHom_sAsm_of_mem (t : SUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (sAsm S t) = t ⟨v, hv⟩ := by
  rw [sAsm_apply, map_prod]
  rw [Finset.prod_eq_single (⟨v, hv⟩ : S)]
  · exact unitAtHom_embUnit_self v (t ⟨v, hv⟩)
  · intro w _ hw
    have hwv : (w.1 : HeightOneSpectrum (𝓞 F)) ≠ v := fun h => hw (Subtype.ext h)
    exact unitAtHom_embUnit_of_ne (Ne.symm hwv) (t w)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unitAtHom_sAsm_of_not_mem (t : SUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (sAsm S t) = 1 := by
  rw [sAsm_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have hwv : (w.1 : HeightOneSpectrum (𝓞 F)) ≠ v := fun h => hv (h ▸ w.2)
  exact unitAtHom_embUnit_of_ne (Ne.symm hwv) (t w)

theorem sAsm_mem_unitsOutside (t : SUnits (F := F) S) : sAsm S t ∈ unitsOutside S :=
  mem_unitsOutside_of_unitAtHom_eq_one S fun _ hv => unitAtHom_sAsm_of_not_mem S t hv

abbrev Q : Type := (InfiniteAdeleRing F)ˣ × (SUnits (F := F) S × DeepUnits (F := F) S)

def asm : Q (F := F) S →* (AdeleRing (𝓞 F) F)ˣ :=
  MonoidHom.coprod archAsm (MonoidHom.coprod (sAsm S) (deepAsm S))

theorem asm_apply (q : Q (F := F) S) : asm S q = archAsm q.1 * (sAsm S q.2.1 * deepAsm S q.2.2) := rfl

theorem continuous_asm : Continuous (asm (F := F) S) := by
  show Continuous fun q : Q (F := F) S => archAsm q.1 * (sAsm S q.2.1 * deepAsm S q.2.2)
  exact (continuous_archAsm.comp continuous_fst).mul
    (((continuous_sAsm S).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_deepAsm S).comp (continuous_snd.comp continuous_snd)))

theorem asm_mem_unitsOutside (q : Q (F := F) S) : asm S q ∈ unitsOutside S :=
  mul_mem (archAsm_mem_unitsOutside S q.1) (mul_mem (sAsm_mem_unitsOutside S q.2.1) (deepAsm_mem_unitsOutside S q.2.2))

theorem archUnits_deepAsm (o : DeepUnits (F := F) S) : archUnits (deepAsm S o) = 1 :=
  Units.ext (deepAsm_val_fst S o)

theorem archUnits_asm (q : Q (F := F) S) : archUnits (asm S q) = q.1 := by
  rw [asm_apply, map_mul, map_mul, archUnits_archAsm, archUnits_sAsm, archUnits_deepAsm, mul_one, mul_one]

theorem unitAtHom_asm_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (asm S q) = q.2.1 ⟨v, hv⟩ := by
  rw [asm_apply, map_mul, map_mul, unitAtHom_archAsm, unitAtHom_sAsm_of_mem S q.2.1 hv,
    unitAtHom_deepAsm_of_mem S q.2.2 hv, one_mul, mul_one]

theorem unitAtHom_asm_of_not_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (asm S q) = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (q.2.2 ⟨v, hv⟩) := by
  rw [asm_apply, map_mul, map_mul, unitAtHom_archAsm, unitAtHom_sAsm_of_not_mem S q.2.1 hv,
    unitAtHom_deepAsm_of_not_mem S q.2.2 hv, one_mul, one_mul]

open scoped Classical in
def deepCoordAt (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) : (v.adicCompletionIntegers F)ˣ :=
  if h : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F then
    { val := ⟨(unitAtHom v x : v.adicCompletion F), h.1⟩
      inv := ⟨(((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), h.2⟩
      val_inv := Subtype.ext (unitAtHom v x).mul_inv
      inv_val := Subtype.ext (unitAtHom v x).inv_mul }
  else 1

open scoped Classical in
theorem deepCoordAt_spec (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ)
    (h : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (deepCoordAt v x) = unitAtHom v x := by
  refine Units.ext ?_
  show (((deepCoordAt v x : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = _
  rw [deepCoordAt, dif_pos h]

def coord (x : (AdeleRing (𝓞 F) F)ˣ) : Q (F := F) S :=
  (archUnits x, (fun v => unitAtHom v.1 x, fun v => deepCoordAt v.1 x))

theorem asm_coord {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) : asm S (coord S u) = u := by
  refine idele_ext (archUnits_asm S _) fun v => ?_
  by_cases hv : v ∈ S
  · exact (unitAtHom_asm_of_mem S (coord S u) hv).trans rfl
  · rw [unitAtHom_asm_of_not_mem S _ hv]
    show Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (deepCoordAt v u) = unitAtHom v u
    rw [mem_unitsOutside_iff] at hu
    refine deepCoordAt_spec v u ⟨?_, ?_⟩
    · exact hu.1 v hv
    · rw [← map_inv]; exact hu.2 v hv

end Assembly2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_TateAssembly2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_TateReference

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set"

open M4aLocalCFT

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

section RangeVal

variable {K : Type*} [GroupWithZero K]

end RangeVal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section CompVal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

variable [MeasurableSpace Kˣ]

end CompVal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

variable {F : Type} [Field F] [NumberField F]

section Instances

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

end Instances
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Deep

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

end Deep
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section SFactor

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

end SFactor
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Arch

def archPiUnits : (InfiniteAdeleRing F)ˣ ≃ₜ* ((w : InfinitePlace F) → (w.Completion)ˣ) :=
  ContinuousMulEquiv.piUnits

omit [NumberField F] in
theorem archPiUnits_apply (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    ((archPiUnits a w : (w.Completion)ˣ) : w.Completion) = (a : InfiniteAdeleRing F) w := rfl

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

end Arch
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Reference

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

end Reference
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Factorwise

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

section DeepConst

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

end DeepConst
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section SProd

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

end SProd
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section ArchProd

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

end ArchProd
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Factorwise
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_TateReference
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_TateFubini

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter"

open M4aLocalCFT

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing AdeleRing.algebraMap_snd_apply Units.rank mk place AdeleRing.algebraMap_fst_apply InfinitePlace.Completion InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing InfinitePlace.Completion.norm_coe TateGlobal.normOneIdeles AdelicVolume.archCentralUnit isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm ideleNorm_pos archUnitHom integralOutside ideleNorm_mul mem_normOneIdeles_iff archUnitHom_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
theorem archPiUnits_archUnits_archUnitHom (w : InfinitePlace F) (u : (w.Completion)ˣ) :
    archPiUnits (archUnits (archUnitHom w u)) = Pi.mulSingle w u := by
  funext w'
  refine Units.ext ?_
  rw [archPiUnits_apply]
  show Function.update (1 : InfiniteAdeleRing F) w (u : w.Completion) w'
    = ((Pi.mulSingle w u : (w' : InfinitePlace F) → (w'.Completion)ˣ) w' : w'.Completion)
  by_cases h : w' = w
  · subst h
    rw [Function.update_self, Pi.mulSingle_eq_same]
  · rw [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    rfl

open scoped Classical in
theorem archAsm_eq_prod_archUnitHom (a : (InfiniteAdeleRing F)ˣ) :
    archAsm a = ∏ w, archUnitHom w (archPiUnits a w) := by
  refine idele_ext ?_ (fun v => ?_)
  · apply (archPiUnits (F := F)).injective
    rw [archUnits_archAsm, map_prod, map_prod]
    simp_rw [archPiUnits_archUnits_archUnitHom]
    exact (Finset.univ_prod_mulSingle _).symm
  · rw [unitAtHom_archAsm, map_prod]
    exact (Finset.prod_eq_one fun w _ => Units.ext rfl).symm

section AlongAsm

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem distribHaarChar_deepAsm (o : DeepUnits (F := F) S) :
    distribHaarChar (AdeleRing (𝓞 F) F) (deepAsm S o) = 1 := by
  refine distribHaarChar_eq_one_of_integral (deepAsm_val_fst S o) (fun w => ?_) (fun w => ?_)
  · rw [deepAsm_val_snd_apply]
    exact SetLike.coe_mem _
  · rw [← map_inv, deepAsm_val_snd_apply]
    exact SetLike.coe_mem _

theorem ideleNorm_asm (q : Q (F := F) S) :
    ideleNorm F (asm S q) = (∏ w, ((distribHaarChar (w.Completion) (archPiUnits q.1 w) : ℝ≥0) : ℝ))
      * ∏ v : S, ((distribHaarChar (v.1.adicCompletion F) (q.2.1 v) : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [asm_apply, map_mul, map_mul, archAsm_eq_prod_archUnitHom, map_prod, sAsm_apply, map_prod,
    distribHaarChar_deepAsm, mul_one]
  simp_rw [distribHaarChar_archUnitHom, distribHaarChar_embUnit_eq_local]
  push_cast
  rfl

end AlongAsm
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section DeepTrivial

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

end DeepTrivial
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Integrands

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

end Integrands
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section LocalIntegrals

section ArchLocal

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion))

end ArchLocal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section FinLocal

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))

end FinLocal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end LocalIntegrals
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Master

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

end Master
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_TateFubini
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_FujisakiC2a

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal NumberField.InfinitePlace IsDedekindDomain M4aHerbrand"

open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory Topology

open scoped NNReal Classical

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC2a

variable {F : Type} [Field F] [NumberField F]

abbrev fiberGroup (F : Type) [Field F] [NumberField F] : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  normOneIdeles F ⊓ unitsOutside (F := F) ∅

theorem fst_apply_mul (a b : AdeleRing (𝓞 F) F) (w : InfinitePlace F) : (a * b).1 w = a.1 w * b.1 w :=
  rfl

theorem fst_apply_one (w : InfinitePlace F) : (1 : AdeleRing (𝓞 F) F).1 w = 1 := rfl

theorem archComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  have h1 : (x : AdeleRing (𝓞 F) F).1 w * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) x.mul_inv
  exact left_ne_zero_of_mul_eq_one h1

theorem norm_archComp_pos (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    0 < ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ :=
  norm_pos_iff.mpr (archComp_ne_zero x w)

theorem norm_algebraMap_fst_apply (x : F) (w : InfinitePlace F) :
    ‖(algebraMap F (AdeleRing (𝓞 F) F) x).1 w‖ = w x := by
  rw [AdeleRing.algebraMap_fst_apply, NumberField.InfinitePlace.Completion.norm_coe]
  rfl

theorem ideleNorm_eq_prod_of_mem_unitsOutside_empty {x : (AdeleRing (𝓞 F) F)ˣ}
    (hx : x ∈ unitsOutside (F := F) ∅) :
    ideleNorm F x
      = ∏ w : InfinitePlace F, ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  have h0 : (∏ v : (↥(∅ : Finset (HeightOneSpectrum (𝓞 F)))),
      ((distribHaarChar (v.1.adicCompletion F) ((coord ∅ x).2.1 v) : ℝ≥0) : ℝ)) = 1 :=
    Fintype.prod_empty _
  rw [← asm_coord ∅ hx, ideleNorm_asm, h0, mul_one, asm_coord ∅ hx]
  refine Finset.prod_congr rfl fun w _ => ?_
  borelize (w.Completion)
  rw [M4aLocalCFT.FujisakiC3.distribHaarChar_completion_eq_pow_mult]
  push_cast
  rfl

def archLog (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) : ℝ :=
  (w.mult : ℝ) * Real.log ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖

theorem archLog_apply (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    archLog x w = (w.mult : ℝ) * Real.log ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ := rfl

theorem archLog_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : archLog (x * y) = archLog x + archLog y := by
  funext w
  rw [Pi.add_apply, archLog_apply, archLog_apply, archLog_apply, Units.val_mul, fst_apply_mul, norm_mul,
    Real.log_mul (norm_archComp_pos x w).ne' (norm_archComp_pos y w).ne', mul_add]

theorem archLog_one : archLog (1 : (AdeleRing (𝓞 F) F)ˣ) = 0 := by
  funext w
  rw [archLog_apply, Units.val_one, fst_apply_one, norm_one, Real.log_one, mul_zero, Pi.zero_apply]

theorem archLog_inv (x : (AdeleRing (𝓞 F) F)ˣ) : archLog x⁻¹ = -archLog x := by
  have h : archLog x⁻¹ + archLog x = 0 := by rw [← archLog_mul, inv_mul_cancel, archLog_one]
  exact eq_neg_of_add_eq_zero_left h

theorem sum_archLog_eq_log_ideleNorm {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ unitsOutside (F := F) ∅) :
    ∑ w, archLog x w = Real.log (ideleNorm F x) := by
  rw [ideleNorm_eq_prod_of_mem_unitsOutside_empty hx, Real.log_prod]
  · simp only [archLog, Real.log_pow]
  · intro w _
    exact pow_ne_zero _ (norm_archComp_pos x w).ne'

theorem sum_archLog_coe_eq_zero (g : ↥(fiberGroup F)) : ∑ w, archLog (g : (AdeleRing (𝓞 F) F)ˣ) w = 0 := by
  rw [sum_archLog_eq_log_ideleNorm (Subgroup.mem_inf.mp g.2).2,
    (mem_normOneIdeles_iff _).mp (Subgroup.mem_inf.mp g.2).1, Real.log_one]

theorem archLog_integralUnitEmb (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    archLog (integralUnitEmb u) w = (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)) := by
  rw [archLog_apply]
  congr 2
  exact norm_algebraMap_fst_apply (algebraMap (𝓞 F) F u) w

theorem archLog_integralUnitEmb_eq_logEmbedding (u : (𝓞 F)ˣ) (w : {w : InfinitePlace F // w ≠ w₀}) :
    archLog (integralUnitEmb u) w.1 = logEmbedding F (Additive.ofMul u) w := by
  rw [archLog_integralUnitEmb, logEmbedding_component]

def logBasis (F : Type) [Field F] [NumberField F] :
    Module.Basis (Fin (NumberField.Units.rank F)) ℝ (logSpace F) :=
  Module.Basis.ofZLatticeBasis ℝ (unitLattice F) (basisUnitLattice F)

abbrev boundR (F : Type) [Field F] [NumberField F] : ℝ :=
  (Fintype.card (InfinitePlace F)) * ∑ i, ‖logBasis F i‖

theorem sum_norm_logBasis_nonneg : 0 ≤ ∑ i, ‖logBasis F i‖ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem exists_unit_norm_sub_logEmbedding_le (v : logSpace F) :
    ∃ u : (𝓞 F)ˣ, ‖v - logEmbedding F (Additive.ofMul u)‖ ≤ ∑ i, ‖logBasis F i‖ := by
  have hfloor : ((ZSpan.floor (logBasis F) v : Submodule.span ℤ (Set.range ⇑(logBasis F))) : logSpace F)
      ∈ unitLattice F :=
    (Module.Basis.ofZLatticeBasis_span ℝ (unitLattice F) (basisUnitLattice F)).le (ZSpan.floor (logBasis F) v).2
  have hfloor' : ((ZSpan.floor (logBasis F) v : Submodule.span ℤ (Set.range ⇑(logBasis F))) : logSpace F)
      ∈ Submodule.map (logEmbedding F).toIntLinearMap ⊤ := hfloor
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp hfloor'
  refine ⟨Additive.toMul y, ?_⟩
  have hfr := ZSpan.norm_fract_le (logBasis F) v
  rw [ZSpan.fract_apply, ← hy] at hfr
  exact hfr

theorem abs_le_card_mul_of_sum_eq_zero (c : InfinitePlace F → ℝ) (hsum : ∑ w, c w = 0)
    {r : ℝ} (hr : 0 ≤ r) (hc : ∀ w : InfinitePlace F, w ≠ w₀ → |c w| ≤ r) (w : InfinitePlace F) :
    |c w| ≤ (Fintype.card (InfinitePlace F)) * r := by
  have hcard : r ≤ (Fintype.card (InfinitePlace F)) * r := by
    nth_rw 1 [← one_mul r]
    exact mul_le_mul_of_nonneg_right (Nat.one_le_cast.mpr Fintype.card_pos) hr
  by_cases hw : w = w₀
  · subst hw
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hsum
    rw [hsum, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ r fun w' _ => hc w'.1 w'.2).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hr
    have hle : (Finset.univ : Finset {w' : InfinitePlace F // w' ≠ w₀}).card
        ≤ Fintype.card (InfinitePlace F) :=
      (Finset.card_univ (α := {w' : InfinitePlace F // w' ≠ w₀})).le.trans (Fintype.card_subtype_le _)
    exact_mod_cast hle
  · exact (hc w hw).trans hcard

omit [NumberField F] in
theorem exp_neg_le_and_le_exp_of_abs_log_le {t R : ℝ} (ht : 0 < t) (h : |Real.log t| ≤ R) :
    Real.exp (-R) ≤ t ∧ t ≤ Real.exp R := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  exact ⟨(Real.exp_le_exp.mpr h1).trans_eq (Real.exp_log ht), (Real.log_le_iff_le_exp ht).mp h2⟩

def annulus (w : InfinitePlace F) (R : ℝ) : Set (w.Completion)ˣ :=
  {t | Real.exp (-R) ≤ ‖(t : w.Completion)‖ ∧ ‖(t : w.Completion)‖ ≤ Real.exp R}

theorem isCompact_annulus_complex (R : ℝ) :
    IsCompact {z : ℂ | Real.exp (-R) ≤ ‖z‖ ∧ ‖z‖ ≤ Real.exp R} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Real.exp R)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.2

omit [NumberField F] in
theorem isCompact_annulus_val (w : InfinitePlace F) (R : ℝ) :
    IsCompact {y : w.Completion | Real.exp (-R) ≤ ‖y‖ ∧ ‖y‖ ≤ Real.exp R} := by
  have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have h := hiso.isClosedEmbedding.isCompact_preimage (isCompact_annulus_complex R)
  refine (congrArg IsCompact ?_).mp h
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, hiso.norm_map_of_map_zero (map_zero _) y]

omit [NumberField F] in
theorem isCompact_annulus (w : InfinitePlace F) (R : ℝ) : IsCompact (annulus w R) := by
  refine Units.isEmbedding_val₀.isCompact_iff.mpr ?_
  refine (congrArg IsCompact ?_).mp (isCompact_annulus_val w R)
  ext y
  constructor
  · intro hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) hy.1)
    exact ⟨Units.mk0 y hy0, hy, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

def archBall (R : ℝ) : Set (InfiniteAdeleRing F)ˣ :=
  {a | ∀ w : InfinitePlace F, Real.exp (-R) ≤ ‖(a : InfiniteAdeleRing F) w‖ ∧
    ‖(a : InfiniteAdeleRing F) w‖ ≤ Real.exp R}

omit [NumberField F] in
theorem archBall_eq_preimage (R : ℝ) :
    archBall (F := F) R = archPiUnits ⁻¹' Set.pi Set.univ (fun w => annulus w R) := by
  ext a
  simp only [archBall, annulus, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, archPiUnits_apply]

omit [NumberField F] in
theorem isCompact_archBall (R : ℝ) : IsCompact (archBall (F := F) R) := by
  rw [archBall_eq_preimage]
  exact (archPiUnits (F := F)).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun w => isCompact_annulus w R)

def paramSet (R : ℝ) : Set (Q (F := F) ∅) :=
  {q | (∏ w : InfinitePlace F, ‖((q.1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ ^ w.mult) = 1}
    ∩ archBall R ×ˢ Set.univ

theorem isCompact_paramSet (R : ℝ) : IsCompact (paramSet (F := F) R) := by
  refine IsCompact.inter_left ((isCompact_archBall R).prod isCompact_univ) ?_
  refine isClosed_eq ?_ continuous_const
  refine continuous_finsetProd _ fun w _ => ?_
  exact (((continuous_apply w).comp (Units.continuous_val.comp continuous_fst)).norm).pow _

theorem asm_mem_of_mem_paramSet {R : ℝ} {q : Q (F := F) ∅} (hq : q ∈ paramSet R) :
    asm ∅ q ∈ fiberGroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, asm_mem_unitsOutside ∅ q⟩
  rw [mem_normOneIdeles_iff, ideleNorm_eq_prod_of_mem_unitsOutside_empty (asm_mem_unitsOutside ∅ q)]
  have h1 : ((asm ∅ q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (q.1 : InfiniteAdeleRing F) :=
    congrArg Units.val (archUnits_asm ∅ q)
  rw [h1]
  exact hq.1

def fiberCompact (F : Type) [Field F] [NumberField F] : Set ↥(fiberGroup F) :=
  Subtype.val ⁻¹' (asm ∅ '' paramSet (boundR F))

theorem val_image_fiberCompact :
    Subtype.val '' fiberCompact F = asm ∅ '' paramSet (boundR F) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨asm ∅ q, asm_mem_of_mem_paramSet hq⟩, ⟨q, hq, rfl⟩, rfl⟩

theorem isCompact_fiberCompact : IsCompact (fiberCompact F) := by
  rw [IsEmbedding.subtypeVal.isCompact_iff, val_image_fiberCompact]
  exact (isCompact_paramSet (boundR F)).image (continuous_asm ∅)

theorem integralUnitEmb_mem (u : (𝓞 F)ˣ) : integralUnitEmb u ∈ fiberGroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · borelize (AdeleRing (𝓞 F) F)
    exact M4aLocalCFT.FujisakiC1.principalIdeles_le_normOneIdeles F (integralUnitEmb_mem_principalIdeles u)
  · have h : integralUnitEmb u ∈ (integralUnitEmb (F := F)).range := ⟨u, rfl⟩
    rw [range_integralUnitEmb] at h
    exact (Subgroup.mem_inf.mp h).2

def unitElem (u : (𝓞 F)ˣ) : ↥(fiberGroup F) := ⟨integralUnitEmb u, integralUnitEmb_mem u⟩

theorem unitElem_mem_subgroupOf (u : (𝓞 F)ˣ) :
    unitElem u ∈ (principalIdeles (𝓞 F) F).subgroupOf (fiberGroup F) := by
  rw [Subgroup.mem_subgroupOf]
  exact integralUnitEmb_mem_principalIdeles u

theorem archLog_mul_unitElem_inv (g₀ : ↥(fiberGroup F)) (u : (𝓞 F)ˣ) (w : {w : InfinitePlace F // w ≠ w₀}) :
    archLog ((g₀ * (unitElem u)⁻¹ : ↥(fiberGroup F)) : (AdeleRing (𝓞 F) F)ˣ) w.1
      = archLog (g₀ : (AdeleRing (𝓞 F) F)ˣ) w.1 - logEmbedding F (Additive.ofMul u) w := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, archLog_mul, archLog_inv, Pi.add_apply, Pi.neg_apply,
    ← sub_eq_add_neg]
  congr 1
  exact archLog_integralUnitEmb_eq_logEmbedding u w

theorem exists_unit_mul_inv_mem_fiberCompact (g₀ : ↥(fiberGroup F)) :
    ∃ u : (𝓞 F)ˣ, g₀ * (unitElem u)⁻¹ ∈ fiberCompact F := by
  obtain ⟨u, hu⟩ := exists_unit_norm_sub_logEmbedding_le (F := F)
    (fun w => archLog (g₀ : (AdeleRing (𝓞 F) F)ˣ) w.1)
  refine ⟨u, ?_⟩
  set g : ↥(fiberGroup F) := g₀ * (unitElem u)⁻¹ with hg
  have hgU : (g : (AdeleRing (𝓞 F) F)ˣ) ∈ unitsOutside (F := F) ∅ := (Subgroup.mem_inf.mp g.2).2
  have hg1 : ideleNorm F (g : (AdeleRing (𝓞 F) F)ˣ) = 1 :=
    (mem_normOneIdeles_iff _).mp (Subgroup.mem_inf.mp g.2).1
  have hbound : ∀ w : InfinitePlace F, |archLog (g : (AdeleRing (𝓞 F) F)ˣ) w| ≤ boundR F := by
    refine abs_le_card_mul_of_sum_eq_zero _ (sum_archLog_coe_eq_zero g) sum_norm_logBasis_nonneg ?_
    intro w hw
    have hcoord : archLog (g : (AdeleRing (𝓞 F) F)ˣ) w
        = ((fun w' : {w' : InfinitePlace F // w' ≠ w₀} => archLog (g₀ : (AdeleRing (𝓞 F) F)ˣ) w'.1)
            - logEmbedding F (Additive.ofMul u)) ⟨w, hw⟩ := by
      rw [Pi.sub_apply, hg]
      exact archLog_mul_unitElem_inv g₀ u ⟨w, hw⟩
    rw [hcoord, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ _).trans hu
  have hann : ∀ w : InfinitePlace F,
      Real.exp (-boundR F) ≤ ‖((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ∧
        ‖((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ≤ Real.exp (boundR F) := by
    intro w
    refine exp_neg_le_and_le_exp_of_abs_log_le (norm_archComp_pos _ w) ?_
    refine le_trans ?_ (hbound w)
    rw [archLog_apply, abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (Nat.one_le_cast.mpr mult_pos)
  refine ⟨coord ∅ (g : (AdeleRing (𝓞 F) F)ˣ), ⟨?_, ?_, Set.mem_univ _⟩, asm_coord ∅ hgU⟩
  · show ∏ w : InfinitePlace F, ‖((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult = 1
    rw [← ideleNorm_eq_prod_of_mem_unitsOutside_empty hgU]
    exact hg1
  · exact fun w => hann w

theorem image_mk_fiberCompact :
    (QuotientGroup.mk : ↥(fiberGroup F) → ↥(fiberGroup F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (fiberGroup F))
      '' fiberCompact F = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨u, hu⟩ := exists_unit_mul_inv_mem_fiberCompact g₀
  exact ⟨_, hu, QuotientGroup.mk_mul_of_mem g₀ (Subgroup.inv_mem _ (unitElem_mem_subgroupOf u))⟩

theorem compactSpace_fiberGroup_quot :
    CompactSpace (↥(fiberGroup F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (fiberGroup F)) := by
  refine ⟨?_⟩
  rw [← image_mk_fiberCompact]
  exact (isCompact_fiberCompact (F := F)).image QuotientGroup.continuous_mk

end M4aLocalCFT.FujisakiC2a
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_FujisakiC2a
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

section Fold_FujisakiC2c

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open IsDedekindDomain FractionalIdeal M4aHerbrand MeasureTheory Topology M4aLocalCFT

open scoped NNReal nonZeroDivisors

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC2c

variable {F : Type} [Field F] [NumberField F]

theorem exists_mul_principal_inv_mem_unitsOutside {x : (AdeleRing (𝓞 F) F)ˣ} (hx : ideleClass x = 1) :
    ∃ α : Fˣ, x * (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α)⁻¹
      ∈ unitsOutside (F := F) ∅ := by
  have hP : (((ideleIdeal x : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F).IsPrincipal := by
    have h := hx
    rw [ideleClass, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff] at h
    exact h
  obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff _).mp hP
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [spanSingleton_zero] at ha
    exact (ideleIdeal x).ne_zero ha
  refine ⟨Units.mk0 a ha0, ?_⟩
  rw [← ker_ideleIdeal, MonoidHom.mem_ker, map_mul, map_inv, ideleIdeal_principal, mul_inv_eq_one]
  ext : 1
  rw [ha, coe_toPrincipalIdeal, Units.val_mk0]

theorem ideleClass_eq_one_of_mem_unitsOutside {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside (F := F) ∅) :
    ideleClass u = 1 := by
  rw [ideleClass, MonoidHom.comp_apply, (ideleIdeal_eq_one_iff u).mpr hu, map_one]

omit [NumberField F] in
theorem exists_norm_pow_mult_eq (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) :
    ∃ t : w.Completion, t ≠ 0 ∧ ‖t‖ ^ w.mult = r := by
  rcases isReal_or_isComplex w with hv | hv
  · refine ⟨(ringEquivRealOfIsReal hv).symm r, ?_, ?_⟩
    · rw [ne_eq, ← map_zero (ringEquivRealOfIsReal hv).symm, (ringEquivRealOfIsReal hv).symm.injective.eq_iff]
      exact hr.ne'
    · have hn : ‖(ringEquivRealOfIsReal hv).symm r‖ = ‖r‖ := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ))
          (ArchMulHaarCompletion.nnnorm_ringEquivReal hv ((ringEquivRealOfIsReal hv).symm r))
        simp only [RingEquiv.apply_symm_apply, coe_nnnorm] at h
        exact h.symm
      rw [mult, if_pos hv, pow_one, hn, Real.norm_eq_abs, abs_of_pos hr]
  · refine ⟨(ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ), ?_, ?_⟩
    · rw [ne_eq, ← map_zero (ringEquivComplexOfIsComplex hv).symm,
        (ringEquivComplexOfIsComplex hv).symm.injective.eq_iff, Complex.ofReal_eq_zero]
      exact fun h => hr.ne' ((Real.sqrt_eq_zero hr.le).mp h)
    · have hn : ‖(ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ)‖ = ‖(Real.sqrt r : ℂ)‖ := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ))
          (ArchMulHaarCompletion.nnnorm_ringEquivComplex hv
            ((ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ)))
        simp only [RingEquiv.apply_symm_apply, coe_nnnorm] at h
        exact h.symm
      rw [mult, if_neg (not_isReal_iff_isComplex.mpr hv), hn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r), Real.sq_sqrt hr.le]

theorem exists_mem_unitsOutside_ideleNorm_eq (r : ℝ) (hr : 0 < r) :
    ∃ y : (AdeleRing (𝓞 F) F)ˣ, y ∈ unitsOutside (F := F) ∅ ∧ ideleNorm F y = r := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨t, ht0, ht⟩ := exists_norm_pow_mult_eq w r hr
  refine ⟨archUnitHom w (Units.mk0 t ht0), ?_, ?_⟩
  · exact mem_unitsOutside_of_unitAtHom_eq_one ∅ fun v _ => Units.ext rfl
  · borelize (w.Completion)
    rw [FujisakiC3.ideleNorm_archUnitHom, Units.val_mk0, ht]

theorem exists_normOne_ideleClass_eq (c : ClassGroup (𝓞 F)) :
    ∃ n : (AdeleRing (𝓞 F) F)ˣ, n ∈ normOneIdeles F ∧ ideleClass n = c := by
  obtain ⟨x, rfl⟩ := ideleClass_surjective' c
  obtain ⟨y, hyU, hy⟩ :=
    exists_mem_unitsOutside_ideleNorm_eq (F := F) (ideleNorm F x)⁻¹ (inv_pos.mpr (ideleNorm_pos x))
  refine ⟨x * y, ?_, ?_⟩
  · rw [mem_normOneIdeles_iff, ideleNorm_mul, hy, mul_inv_cancel₀ (ideleNorm_pos x).ne']
  · rw [map_mul, ideleClass_eq_one_of_mem_unitsOutside hyU, mul_one]

theorem fiberGroup_le_normOneIdeles : FujisakiC2a.fiberGroup F ≤ normOneIdeles F := inf_le_left

def inclHom : ↥(FujisakiC2a.fiberGroup F) →* ↥(normOneIdeles F) :=
  Subgroup.inclusion fiberGroup_le_normOneIdeles

theorem continuous_inclHom : Continuous (inclHom (F := F)) := by
  show Continuous fun x : ↥(FujisakiC2a.fiberGroup F) =>
    (⟨(x : (AdeleRing (𝓞 F) F)ˣ), fiberGroup_le_normOneIdeles x.2⟩ : ↥(normOneIdeles F))
  exact continuous_subtype_val.subtype_mk _

def fiberMap :
    ↥(FujisakiC2a.fiberGroup F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (FujisakiC2a.fiberGroup F) →*
      ↥(normOneIdeles F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F) :=
  QuotientGroup.map _ _ inclHom fun g hg => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, inclHom, Subgroup.coe_inclusion]
    exact Subgroup.mem_subgroupOf.mp hg

theorem continuous_fiberMap : Continuous (fiberMap (F := F)) := by
  rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
  have h : (⇑(fiberMap (F := F)) ∘ QuotientGroup.mk) = QuotientGroup.mk ∘ ⇑(inclHom (F := F)) := by
    funext x
    rfl
  rw [h]
  exact QuotientGroup.continuous_mk.comp continuous_inclHom

theorem isCompact_range_fiberMap : IsCompact (Set.range (fiberMap (F := F))) := by
  haveI := FujisakiC2a.compactSpace_fiberGroup_quot (F := F)
  exact isCompact_range continuous_fiberMap

theorem compactSpace_normOneIdeleClass_impl (F : Type) [Field F] [NumberField F] :
    CompactSpace (↥(normOneIdeles F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) := by
  borelize (AdeleRing (𝓞 F) F)
  choose rep hrep using fun c : ClassGroup (𝓞 F) => exists_normOne_ideleClass_eq (F := F) c
  set K : Set (↥(normOneIdeles F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) :=
    ⋃ c : ClassGroup (𝓞 F),
      (fun y => (QuotientGroup.mk (⟨rep c, (hrep c).1⟩ : ↥(normOneIdeles F)) : ↥(normOneIdeles F) ⧸
        (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) * y) '' Set.range (fiberMap (F := F))
  have hKc : IsCompact K :=
    isCompact_iUnion fun c => (isCompact_range_fiberMap (F := F)).image (continuous_const_mul _)
  have hKuniv : K = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    set c : ClassGroup (𝓞 F) := ideleClass (n : (AdeleRing (𝓞 F) F)ˣ) with hc
    have h1 : ideleClass ((n : (AdeleRing (𝓞 F) F)ˣ) * (rep c)⁻¹) = 1 := by
      rw [map_mul, map_inv, (hrep c).2, hc, mul_inv_cancel]
    obtain ⟨α, hU⟩ := exists_mul_principal_inv_mem_unitsOutside h1
    set p : (AdeleRing (𝓞 F) F)ˣ := (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α) with hp
    have hpP : p ∈ principalIdeles (𝓞 F) F := ⟨α, rfl⟩
    have hpN : p ∈ normOneIdeles F := FujisakiC1.principalIdeles_le_normOneIdeles F hpP
    have huU : (rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹) ∈ unitsOutside (F := F) ∅ := by
      rwa [mul_comm (n : (AdeleRing (𝓞 F) F)ˣ) (rep c)⁻¹, mul_assoc] at hU
    have huN : (rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹) ∈ normOneIdeles F :=
      (normOneIdeles F).mul_mem ((normOneIdeles F).inv_mem (hrep c).1)
        ((normOneIdeles F).mul_mem n.2 ((normOneIdeles F).inv_mem hpN))
    let g : ↥(FujisakiC2a.fiberGroup F) :=
      ⟨(rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹), Subgroup.mem_inf.mpr ⟨huN, huU⟩⟩
    refine Set.mem_iUnion.mpr ⟨c, fiberMap (QuotientGroup.mk g), ⟨QuotientGroup.mk g, rfl⟩, ?_⟩
    show QuotientGroup.mk (⟨rep c, (hrep c).1⟩ : ↥(normOneIdeles F)) * fiberMap (QuotientGroup.mk g)
      = QuotientGroup.mk n
    rw [fiberMap, QuotientGroup.map_mk, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((rep c * ((rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹)))⁻¹ * (n : (AdeleRing (𝓞 F) F)ˣ))
      ∈ principalIdeles (𝓞 F) F
    rw [mul_inv_cancel_left, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    exact hpP
  refine ⟨?_⟩
  rw [← hKuniv]
  exact hKc

end M4aLocalCFT.FujisakiC2c
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

end Fold_FujisakiC2c
p2m_reactivate "P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.M4aLocalCFT P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField.TateGlobal"

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.NumberField M4aHerbrand"

theorem solution (F : Type) [Field F] [NumberField F] :
    CompactSpace (↥(NumberField.TateGlobal.normOneIdeles F) ⧸
      (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)) :=
  M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl F

#print axioms solution

end S_NumberField_TateGlobal_compactSpace_normOneIdeleClass
end P2MW
export P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass (solution)
