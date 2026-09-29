-- Prove2me | solution 1 for NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/16a8e4d2-8d2f-5106-a2eb-df49cb8d6d8f

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq

set_option autoImplicit false
set_option Elab.async false

section Fold_TateSDecomp

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel IsDedekindDomain"

open scoped NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem mem_integralOutside_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (x : AdeleRing (𝓞 F) F) :
    x ∈ integralOutside S ↔ ∀ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem one_mem_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (1 : AdeleRing (𝓞 F) F) ∈ integralOutside S :=
  fun v _ => (v.adicCompletionIntegers F).one_mem

theorem mul_mem_integralOutside {S : Finset (HeightOneSpectrum (𝓞 F))} {x y : AdeleRing (𝓞 F) F}
    (hx : x ∈ integralOutside S) (hy : y ∈ integralOutside S) : x * y ∈ integralOutside S :=
  fun v hv => mul_mem (hx v hv) (hy v hv)

theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (F := F) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    Fact.out (p := fun v => v ∉ S)
  exact h.preimage (continuous_adeleFin (𝓞 F) F)

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

theorem isOpen_unitsOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (unitsOutside (F := F) S : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have h1 : IsOpen ((fun x : (AdeleRing (𝓞 F) F)ˣ => (x : AdeleRing (𝓞 F) F)) ⁻¹' integralOutside S) :=
    (isOpen_integralOutside S).preimage Units.continuous_val
  have h2 : IsOpen ((fun x : (AdeleRing (𝓞 F) F)ˣ => ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      ⁻¹' integralOutside S) :=
    (isOpen_integralOutside S).preimage Units.continuous_coe_inv
  exact h1.inter h2

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

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel IsDedekindDomain"

open scoped NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

def unitAtHom (w : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* (w.adicCompletion F)ˣ :=
  Units.map (((finAdeleEval (𝓞 F) F w).comp (adeleFin (𝓞 F) F)).toMonoidHom)

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

theorem ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : ordAt v t⁻¹ = -ordAt v t := by
  simp [ordAt, ofMul_inv, map_neg]

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

theorem unifPow_val_fst (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ((unifPow ϖ k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  let archU : (AdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ := Units.map (adeleArch (𝓞 F) F).toMonoidHom
  have h1 : ∀ v, archU (embUnit v (ϖ.ϖ v)) = 1 := fun v => Units.ext (embUnit_val_fst v (ϖ.ϖ v))
  have h : archU (unifPow ϖ k) = 1 := by
    rw [unifPow, Finsupp.prod, map_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [map_zpow, h1, one_zpow]
  exact congrArg (fun u : (InfiniteAdeleRing F)ˣ => (u : InfiniteAdeleRing F)) h

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

theorem expVec_apply_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : expVec S x v = 0 := by
  classical
  simp [expVec, Finsupp.ofSupportFinite_coe, hv]

theorem expVec_apply_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (x : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : expVec S x v = ordAt v (unitAtHom v x) := by
  classical
  simp [expVec, Finsupp.ofSupportFinite_coe, hv]

def unitPart (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (AdeleRing (𝓞 F) F)ˣ :=
  (unifPow ϖ (expVec S x))⁻¹ * x

theorem unifPow_mul_unitPart (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    unifPow ϖ (expVec S x) * unitPart ϖ S x = x := by
  rw [unitPart, mul_inv_cancel_left]

theorem ordAt_unitAtHom_unitPart_of_not_mem (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (x : (AdeleRing (𝓞 F) F)ˣ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ordAt v (unitAtHom v (unitPart ϖ S x)) = 0 := by
  rw [unitPart, map_mul, map_inv, ordAt_mul, ordAt_inv, ordAt_unitAtHom_unifPow, expVec_apply_of_not_mem x hv]
  ring

theorem unitPart_mem_unitsOutside (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : (AdeleRing (𝓞 F) F)ˣ) : unitPart ϖ S x ∈ unitsOutside S := by
  rw [mem_unitsOutside_iff]
  have key : ∀ v ∉ S, ((unitAtHom v (unitPart ϖ S x) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v (unitPart ϖ S x))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        ∈ v.adicCompletionIntegers F :=
    fun v hv => (ordAt_eq_zero_iff v _).mp (ordAt_unitAtHom_unitPart_of_not_mem ϖ x hv)
  refine ⟨fun v hv => (key v hv).1, fun v hv => ?_⟩
  have h := (key v hv).2
  rwa [← map_inv] at h

def archUnits : (AdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ := Units.map (adeleArch (𝓞 F) F).toMonoidHom

theorem char_unifPow (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    χ (unifPow ϖ k) = k.prod fun v n => localChar χ v (ϖ.ϖ v) ^ n := by
  rw [unifPow, Finsupp.prod, map_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow]
  rfl

end NumberField.TateGlobal

end

end Fold_TateSDecomp2

section Fold_TateSDecomp3

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory Set Filter Topology"

open scoped NNReal Pointwise

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F := by
  have e := (Module.finBasis ℚ F).equivFun.toEquiv
  exact (Equiv.countable_iff e).mpr inferInstance

theorem countable_heightOneSpectrum (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := countable_numberField F
  haveI : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  haveI : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  haveI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

attribute [local instance] countable_heightOneSpectrum

def ExpIndex (S : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  {k : HeightOneSpectrum (𝓞 F) →₀ ℤ // ∀ v ∈ S, k v = 0}

scoped instance (S : Finset (HeightOneSpectrum (𝓞 F))) : Countable (ExpIndex (F := F) S) := by
  unfold ExpIndex; infer_instance

def shell (S : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {x | expVec S x = k}

theorem expVec_unifPow_mul (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    expVec S (unifPow ϖ k * u) = k := by
  have hu' := (mem_unitsOutside_iff S u).mp hu
  ext v
  by_cases hv : v ∈ S
  · rw [expVec_apply_of_mem _ hv, hk v hv]
  · rw [expVec_apply_of_not_mem _ hv, map_mul, ordAt_mul, ordAt_unitAtHom_unifPow]
    have h0 : ordAt v (unitAtHom v u) = 0 := by
      rw [ordAt_eq_zero_iff]
      refine ⟨hu'.1 v hv, ?_⟩
      rw [← map_inv]
      exact hu'.2 v hv
    rw [h0, add_zero]

theorem expVec_vanishes (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∀ v ∈ S, expVec S x v = 0 := fun _ hv => expVec_apply_of_mem x hv

theorem shell_eq_smul (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) :
    shell S k = unifPow ϖ k • (unitsOutside (F := F) S : Set (AdeleRing (𝓞 F) F)ˣ) := by
  ext x
  constructor
  · intro hx
    refine ⟨unitPart ϖ S x, unitPart_mem_unitsOutside ϖ S x, ?_⟩
    show unifPow ϖ k * unitPart ϖ S x = x
    have h := unifPow_mul_unitPart ϖ S x
    rw [show expVec S x = k from hx] at h
    exact h
  · rintro ⟨u, hu, rfl⟩
    exact expVec_unifPow_mul ϖ hk hu

theorem isOpen_shell (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) : IsOpen (shell (F := F) S k) := by
  rw [shell_eq_smul ϖ hk]
  exact (isOpen_unitsOutside S).smul _

theorem measurableSet_shell [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) : MeasurableSet (shell (F := F) S k) :=
  (isOpen_shell ϖ hk).measurableSet

theorem pairwise_disjoint_shell (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Pairwise (Function.onFun Disjoint fun k : ExpIndex (F := F) S => shell S k.1) := by
  intro k k' hne
  refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
  exact Subtype.ext (hx.symm.trans hx')

theorem iUnion_shell (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ⋃ k : ExpIndex (F := F) S, shell S k.1 = univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
  exact ⟨⟨expVec S x, expVec_vanishes S x⟩, rfl⟩

section Integral

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem setIntegral_smul_eq (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    {U : Set (AdeleRing (𝓞 F) F)ˣ} (hU : MeasurableSet U) (g : (AdeleRing (𝓞 F) F)ˣ) (G : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    ∫ x in g • U, G x ∂ν = ∫ u in U, G (g * u) ∂ν := by
  have hgU : MeasurableSet (g • U) := hU.const_smul g
  rw [← integral_indicator hgU, ← integral_indicator hU, ← integral_mul_left_eq_self _ g]
  congr 1
  funext u
  have hiff : g * u ∈ g • U ↔ u ∈ U := by
    constructor
    · intro h
      obtain ⟨u', hu', h'⟩ := Set.mem_smul_set.mp h
      rw [smul_eq_mul] at h'
      rw [← mul_left_cancel h']
      exact hu'
    · intro hu
      exact Set.mem_smul_set.mpr ⟨u, hu, rfl⟩
  simp only [Set.indicator]
  by_cases hu : u ∈ U
  · rw [if_pos (hiff.mpr hu), if_pos hu]
  · rw [if_neg (mt hiff.mp hu), if_neg hu]

theorem hasSum_setIntegral_unitsOutside (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    (ϖ : Uniformizers F) (S : Finset (HeightOneSpectrum (𝓞 F))) {G : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hG : Integrable G ν) :
    HasSum (fun k : ExpIndex (F := F) S => ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), G (unifPow ϖ k.1 * u) ∂ν)
      (∫ x, G x ∂ν) := by
  have h := hasSum_integral_iUnion (μ := ν) (f := G) (s := fun k : ExpIndex (F := F) S => shell S k.1)
    (fun k => measurableSet_shell ϖ k.2) (pairwise_disjoint_shell S)
    (by rw [iUnion_shell]; exact hG.integrableOn)
  rw [iUnion_shell, Measure.restrict_univ] at h
  refine h.congr_fun fun k => ?_
  show _ = ∫ x in shell S k.1, G x ∂ν
  rw [shell_eq_smul ϖ k.2, setIntegral_smul_eq ν (isOpen_unitsOutside S).measurableSet]

end Integral

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end Fold_TateSDecomp3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Fold_TateAssembly

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel IsDedekindDomain Topology TopologicalSpace Set"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

scoped instance instSecondCountableUnitsAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

scoped instance instSecondCountableCompletion (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableUnitsCompletion (w : InfinitePlace F) : SecondCountableTopology (w.Completion)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) :=
  show SecondCountableTopology ((w : InfinitePlace F) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X] [SecondCountableTopology X] :
    SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance instSecondCountableUnitsInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F)ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instSecondCountableUnitsIntegers (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletionIntegers F)ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

section Assembly

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev DeepUnits : Type := (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) → (v.1.adicCompletionIntegers F)ˣ

abbrev SUnits : Type := (v : S) → (v.1.adicCompletion F)ˣ

scoped instance instSecondCountableDeepUnits : SecondCountableTopology (DeepUnits (F := F) S) := by
  haveI : Countable {v : HeightOneSpectrum (𝓞 F) // v ∉ S} := by
    haveI := countable_heightOneSpectrum F
    infer_instance
  infer_instance

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end Fold_TateAssembly
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Fold_TateAssembly2

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel IsDedekindDomain Topology TopologicalSpace Set Filter"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

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

theorem deepCoordAt_of_map (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) (o : (v.adicCompletionIntegers F)ˣ)
    (h : unitAtHom v x = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom o) : deepCoordAt v x = o := by
  have hmem : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [h, ← map_inv]
    exact ⟨SetLike.coe_mem _, SetLike.coe_mem _⟩
  have h2 := deepCoordAt_spec v x hmem
  rw [h] at h2
  refine Units.ext (Subtype.ext ?_)
  have h3 := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) h2
  exact h3

def coord (x : (AdeleRing (𝓞 F) F)ˣ) : Q (F := F) S :=
  (archUnits x, (fun v => unitAtHom v.1 x, fun v => deepCoordAt v.1 x))

theorem coord_asm (q : Q (F := F) S) : coord S (asm S q) = q := by
  obtain ⟨a, t, o⟩ := q
  refine Prod.ext (archUnits_asm S _) (Prod.ext (funext fun v => ?_) (funext fun v => ?_))
  · show unitAtHom v.1 (asm S (a, t, o)) = t v
    rw [unitAtHom_asm_of_mem S (a, t, o) v.2]
  · show deepCoordAt v.1 (asm S (a, t, o)) = o v
    exact deepCoordAt_of_map v.1 _ (o v) (unitAtHom_asm_of_not_mem S (a, t, o) v.2)

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

theorem range_asm : Set.range (asm (F := F) S) = unitsOutside S := by
  ext u
  constructor
  · rintro ⟨q, rfl⟩; exact asm_mem_unitsOutside S q
  · intro hu; exact ⟨coord S u, asm_coord S hu⟩

theorem continuous_unitAtHom (v : HeightOneSpectrum (𝓞 F)) : Continuous (unitAtHom (F := F) v) :=
  Units.continuous_map ((continuous_finAdeleEval (𝓞 F) F v).comp (continuous_adeleFin (𝓞 F) F))

theorem continuous_archUnits : Continuous (archUnits (F := F)) :=
  Units.continuous_map (continuous_adeleArch (𝓞 F) F)

theorem continuousOn_deepCoordAt {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ContinuousOn (deepCoordAt (F := F) v) (unitsOutside S) := by
  classical
  have key : ∀ u ∈ (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
      (unitAtHom v u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
        (((unitAtHom v u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro u hu
    have hu' := (mem_unitsOutside_iff S u).mp hu
    refine ⟨hu'.1 v hv, ?_⟩
    rw [← map_inv]; exact hu'.2 v hv
  rw [continuousOn_iff_continuous_restrict]
  have c1 : Continuous fun u : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) =>
      (⟨(unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F), (key u u.2).1⟩ : v.adicCompletionIntegers F) :=
    (Units.continuous_val.comp ((continuous_unitAtHom v).comp continuous_subtype_val)).subtype_mk _
  have c2 : Continuous fun u : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) =>
      (⟨(((unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), (key u u.2).2⟩ :
        v.adicCompletionIntegers F) :=
    (Units.continuous_coe_inv.comp ((continuous_unitAtHom v).comp continuous_subtype_val)).subtype_mk _
  refine Units.continuous_iff.mpr ⟨c1.congr fun u => ?_, c2.congr fun u => ?_⟩
  · refine Subtype.ext ?_
    show (unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F)
      = (((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ) : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
    rw [deepCoordAt, dif_pos (key u u.2)]
  · refine Subtype.ext ?_
    have e : ((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletionIntegers F)ˣ)
        = (deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ := rfl
    show (((unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
    rw [deepCoordAt, dif_pos (key u u.2)]
    rfl

theorem continuousOn_coord : ContinuousOn (coord (F := F) S) (unitsOutside S) := by
  have h1 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => archUnits x) (unitsOutside S) :=
    continuous_archUnits.continuousOn
  have h2 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => fun v : S => unitAtHom v.1 x) (unitsOutside S) :=
    (continuous_pi fun v : S => continuous_unitAtHom (F := F) v.1).continuousOn
  have h3 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      deepCoordAt v.1 x) (unitsOutside S) :=
    continuousOn_pi.mpr fun v => continuousOn_deepCoordAt S v.2
  exact h1.prodMk (h2.prodMk h3)

def asmHomeo : Q (F := F) S ≃ₜ (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) where
  toFun q := ⟨asm S q, asm_mem_unitsOutside S q⟩
  invFun u := coord S u
  left_inv q := coord_asm S q
  right_inv u := Subtype.ext (asm_coord S u.2)
  continuous_toFun := (continuous_asm S).subtype_mk _
  continuous_invFun := continuousOn_iff_continuous_restrict.mp (continuousOn_coord S)

theorem isOpenEmbedding_asm : IsOpenEmbedding (asm (F := F) S) := by
  have h : (⇑(asm (F := F) S) : Q (F := F) S → (AdeleRing (𝓞 F) F)ˣ)
      = fun q : Q (F := F) S => ((asmHomeo S q : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F)ˣ) :=
    funext fun _ => rfl
  rw [h]
  exact (isOpen_unitsOutside S).isOpenEmbedding_subtypeVal.comp (asmHomeo S).isOpenEmbedding

end Assembly2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end Fold_TateAssembly2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Fold_TateAssembly3

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain MeasureTheory Topology Set"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

section Pullback

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

variable [MeasurableSpace (Q (F := F) S)] [BorelSpace (Q (F := F) S)]

theorem measurableEmbedding_asm : MeasurableEmbedding (asm (F := F) S) :=
  (isOpenEmbedding_asm S).measurableEmbedding

def asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) : Measure (Q (F := F) S) := ν.comap (asm S)

theorem asmMeasure_apply (ν : Measure (AdeleRing (𝓞 F) F)ˣ) (s : Set (Q (F := F) S)) :
    asmMeasure S ν s = ν (asm S '' s) :=
  (measurableEmbedding_asm S).comap_apply ν s

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] [MeasurableSpace (Q (F := F) S)]
  [BorelSpace (Q (F := F) S)] in
theorem image_preimage_mul_left (g : Q (F := F) S) (A : Set (Q (F := F) S)) :
    asm S '' ((fun q => g * q) ⁻¹' A) = (fun x => asm S g * x) ⁻¹' (asm S '' A) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨g * q, hq, by rw [map_mul]⟩
  · rintro ⟨q', hq', hx⟩
    refine ⟨g⁻¹ * q', ?_, ?_⟩
    · show g * (g⁻¹ * q') ∈ A
      rwa [mul_inv_cancel_left]
    · apply mul_left_cancel (a := asm S g)
      rw [← map_mul, mul_inv_cancel_left, hx]

scoped instance isMulLeftInvariant_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] :
    (asmMeasure S ν).IsMulLeftInvariant := by
  refine (forall_measure_preimage_mul_iff _).mp fun g A _ => ?_
  rw [asmMeasure_apply, asmMeasure_apply, image_preimage_mul_left]
  exact measure_preimage_mul ν (asm S g) _

scoped instance isFiniteMeasureOnCompacts_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (asmMeasure S ν) := by
  refine ⟨fun K hK => ?_⟩
  rw [asmMeasure_apply]
  exact (hK.image (continuous_asm S)).measure_lt_top

scoped instance isOpenPosMeasure_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsOpenPosMeasure] :
    (asmMeasure S ν).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [asmMeasure_apply]
  exact ((isOpenEmbedding_asm S).isOpenMap U hU).measure_ne_zero ν (hne.image _)

scoped instance isHaarMeasure_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    (asmMeasure S ν).IsHaarMeasure where

theorem setIntegral_unitsOutside_eq_integral_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (G : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    ∫ x in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), G x ∂ν = ∫ q, G (asm S q) ∂(asmMeasure S ν) := by
  rw [← range_asm S, ← (measurableEmbedding_asm S).map_comap ν]
  exact (measurableEmbedding_asm S).integral_map G

end Pullback
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end Fold_TateAssembly3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Fold_LocalHaarModulus

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end LocalHaarModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end Fold_LocalHaarModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Fold_LocalZetaUnramified

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open LanglandsTunnell.TateLocal

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

theorem ord_piUnit_pow (hϖ : Irreducible ϖ) (k : ℕ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul ((piUnit hϖ) ^ k)) = k := by
  have h : Additive.ofMul ((piUnit hϖ) ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_nsmul, ord_piUnit]
  simp

def shellSet (hϖ : Irreducible ϖ) (k : ℕ) : Set (v.adicCompletion F) :=
  (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    \ (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))

theorem isCompact_integers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  NumberField.isCompactAdicCompletionIntegers F v

theorem isCompact_smul_integers (c : v.adicCompletion F) :
    IsCompact (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have h := (isCompact_integers (F := F) (v := v)).image (continuous_const_smul c)
  rwa [Set.image_smul] at h

theorem measurableSet_smul_integers [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (c : v.adicCompletion F) :
    MeasurableSet (c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  (isCompact_smul_integers c).isClosed.measurableSet

theorem measurableSet_shellSet [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (hϖ : Irreducible ϖ) (k : ℕ) :
    MeasurableSet (shellSet hϖ k) :=
  (measurableSet_smul_integers _).diff (measurableSet_smul_integers _)

theorem mem_smul_integers_iff {c x : v.adicCompletion F} :
    x ∈ c • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ↔ ∃ y : v.adicCompletionIntegers F, c * (y : v.adicCompletion F) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, (smul_eq_mul c y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨(y : v.adicCompletion F), y.2, by show c • (y : v.adicCompletion F) = x; rw [smul_eq_mul]; exact hy⟩

theorem shellSet_subset_integers (hϖ : Irreducible ϖ) (k : ℕ) :
    shellSet hϖ k ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hx.1
  rw [← hy]
  push_cast [piUnit_val]
  exact mul_mem (pow_mem ϖ.2 k) y.2

theorem zero_notMem_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : (0 : v.adicCompletion F) ∉ shellSet hϖ k := by
  intro h
  exact h.2 (mem_smul_integers_iff.mpr ⟨0, by push_cast; ring⟩)

theorem mem_shellSet_iff_ord_eq (hϖ : Irreducible ϖ) (k : ℕ) {x : v.adicCompletion F} (hx : x ≠ 0) :
    x ∈ shellSet hϖ k
      ↔ ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx))
          = k := by
  constructor
  · intro hmem
    obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hmem.1
    have hy0 : (y : v.adicCompletion F) ≠ 0 := by
      intro h0
      exact hx (by rw [← hy, h0, mul_zero])
    have hyunit : IsUnit y := by
      by_contra hnu
      have hymem : y ∈ maximalIdeal (v.adicCompletionIntegers F) := hnu
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hymem
      obtain ⟨z, hz⟩ := hymem
      refine hmem.2 (mem_smul_integers_iff.mpr ⟨z, ?_⟩)
      rw [← hy, hz]
      push_cast [pow_succ, piUnit_val]
      ring
    obtain ⟨u, hu⟩ := hyunit
    have hxfac : Units.mk0 x hx
        = piUnit hϖ ^ k
          * Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u := by
      ext
      rw [Units.val_mk0, ← hy]
      push_cast [piUnit_val, Units.coe_map]
      rw [← hu]
      rfl
    have hordu : ValuationOrd.ord (v.adicCompletionIntegers F)
        (Additive.ofMul (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u))
          = 0 :=
      (ValuationOrd.ord_eq_zero_iff _ _).mpr ⟨u, rfl⟩
    have hsplit : Additive.ofMul (Units.mk0 x hx)
        = Additive.ofMul (piUnit hϖ ^ k)
          + Additive.ofMul (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) u) := by
      rw [hxfac]; rfl
    rw [hsplit, map_add, hordu, add_zero, ord_piUnit_pow]
  · intro hord
    set w : (v.adicCompletion F)ˣ := Units.mk0 x hx * (piUnit hϖ ^ k)⁻¹ with hwdef
    have hword : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 := by
      have hsub : Additive.ofMul w = Additive.ofMul (Units.mk0 x hx)
          - Additive.ofMul (piUnit hϖ ^ k) := rfl
      rw [hsub, map_sub, hord, ord_piUnit_pow, sub_self]
    obtain ⟨u, hu⟩ := (ValuationOrd.ord_eq_zero_iff _ _).mp hword
    have hxw : x = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      have hfac : Units.mk0 x hx = piUnit hϖ ^ k * w := by
        rw [hwdef, mul_comm (Units.mk0 x hx) ((piUnit hϖ ^ k)⁻¹), mul_inv_cancel_left]
      calc x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
        _ = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
              rw [hfac, Units.val_mul]
    constructor
    · have hwmem : ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          ∈ v.adicCompletionIntegers F := by
        rw [← hu]
        exact ((u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
      exact mem_smul_integers_iff.mpr
        ⟨⟨((w : (v.adicCompletion F)ˣ) : v.adicCompletion F), hwmem⟩, hxw.symm⟩
    · intro hnext
      obtain ⟨z, hz⟩ := mem_smul_integers_iff.mp hnext
      have hcan : ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          * ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          = ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            * (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * (z : v.adicCompletion F)) := by
        rw [← hxw, ← hz]
        push_cast [pow_succ, piUnit_val]
        ring
      have hwz := mul_left_cancel₀ (Units.ne_zero (piUnit hϖ ^ k)) hcan
      have hwmem : ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
        rw [hwz]; exact mul_mem ϖ.2 z.2
      obtain ⟨uw, huw⟩ := (ValuationOrd.ord_eq_zero_iff _ _).mp hword
      have huwO : ((uw : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          = ϖ * z := by
        apply Subtype.coe_injective
        push_cast
        calc ((uw : (v.adicCompletionIntegers F)ˣ) : v.adicCompletion F)
            = ((Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom) uw
                : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
          _ = ((w : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by rw [huw]
          _ = _ := by rw [hwz]
      have hunit : IsUnit ((ϖ : v.adicCompletionIntegers F) * z) := huwO ▸ uw.isUnit
      exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left hunit)

end Shells
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Measures

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

omit [BorelSpace (v.adicCompletion F)] [μ.Regular] in
theorem measure_integers_lt_top : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ :=
  (isCompact_integers (F := F) (v := v)).measure_lt_top

end Measures
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Integrand

variable {ϖ : v.adicCompletionIntegers F}

end Integrand
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

section Zeta

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end Zeta
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

end LocalZetaUnramified
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_LocalZetaUnramified
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_MulHaarFromAdditive

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace MulHaarFromAdditive

open LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem _root_.M4aLocalCFT.MulHaarFromAdditive.isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have hr : Set.range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F)
      = {(0 : v.adicCompletion F)}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [hr]
  exact isClosed_singleton.isOpen_compl

p2m_export "M4aLocalCFT.MulHaarFromAdditive" "isOpenEmbedding_val"
theorem image_val_subset_compl_zero (A : Set (v.adicCompletion F)ˣ) :
    (Units.val '' A) ⊆ {(0 : v.adicCompletion F)}ᶜ := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

theorem smul_set_eq_preimage {c : v.adicCompletion F} (hc : c ≠ 0)
    (S : Set (v.adicCompletion F)) :
    c • S = (fun y => c⁻¹ * y) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

theorem isOpen_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : IsOpen S) :
    IsOpen (c • S) := by
  have h : c • S = (Homeomorph.mulLeft₀ c hc) '' S := by
    ext x
    simp [Homeomorph.coe_mulLeft₀, Set.mem_smul_set, smul_eq_mul, Set.mem_image]
  rw [h]
  exact (Homeomorph.mulLeft₀ c hc).isOpenMap _ hS

theorem image_val_smul (g : (v.adicCompletion F)ˣ) (A : Set (v.adicCompletion F)ˣ) :
    Units.val '' (g • A) = (g : v.adicCompletion F) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(a : v.adicCompletion F), ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨g * a, ⟨a, ha, rfl⟩, by simp [smul_eq_mul]⟩

variable {ϖ : v.adicCompletionIntegers F}

theorem isOpen_shellSet (hϖ : Irreducible ϖ) (k : ℕ) : IsOpen (shellSet hϖ k) := by
  unfold shellSet
  refine IsOpen.sdiff (isOpen_smul_set (Units.ne_zero _) ?_) ?_
  · exact Valued.isOpen_valuationSubring _
  · rw [smul_set_eq_preimage (Units.ne_zero _)]
    exact (Valued.isClosed_valuationSubring _).preimage (continuous_const_mul _)

theorem one_mem_shellSet_zero (hϖ : Irreducible ϖ) :
    (1 : v.adicCompletion F) ∈ shellSet hϖ 0 := by
  have h10 : (1 : v.adicCompletion F) ≠ 0 := one_ne_zero
  rw [mem_shellSet_iff_ord_eq hϖ 0 h10]
  have h1 : Units.mk0 (1 : v.adicCompletion F) h10 = 1 := Units.ext (by simp)
  rw [h1]
  simp

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

def genShell (hϖ : Irreducible ϖ) (k : ℤ) : Set (v.adicCompletion F) :=
  ((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0

theorem mem_genShell_iff (hϖ : Irreducible ϖ) {k : ℤ} {x : v.adicCompletion F} (hx : x ≠ 0) :
    x ∈ genShell hϖ k
      ↔ ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx)) = k := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    have hu : Units.mk0 _ hx = piUnit hϖ ^ k * Units.mk0 y hy0 :=
      Units.ext (by simp [smul_eq_mul])
    rw [hu, ord_ofMul_mul, ord_ofMul_zpow_piUnit hϖ,
      (mem_shellSet_iff_ord_eq hϖ 0 hy0).mp hy]
    simp
  · intro hord
    have hne : (((piUnit hϖ ^ k)⁻¹ * Units.mk0 x hx : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) ≠ 0 := Units.ne_zero _
    refine ⟨_, (mem_shellSet_iff_ord_eq hϖ 0 hne).mpr ?_, ?_⟩
    · have hmk : Units.mk0 _ hne = (piUnit hϖ ^ k)⁻¹ * Units.mk0 x hx :=
        Units.ext (by simp)
      rw [hmk, ord_ofMul_mul,
        show ((piUnit hϖ ^ k)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hϖ ^ (-k) from
          (zpow_neg _ _).symm,
        ord_ofMul_zpow_piUnit hϖ, hord]
      simp
    · show (↑(piUnit hϖ ^ k) : v.adicCompletion F) • _ = x
      rw [smul_eq_mul, ← Units.val_mul, mul_inv_cancel_left, Units.val_mk0]

theorem genShell_disjoint (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint (genShell hϖ)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  rintro x hxk hxl
  have hx : x ≠ 0 := by
    rcases hxk with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [smul_eq_mul]
    exact mul_ne_zero (Units.ne_zero _) hy0
  exact hkl (((mem_genShell_iff hϖ hx).mp hxk).symm.trans ((mem_genShell_iff hϖ hx).mp hxl))

theorem iUnion_genShell (hϖ : Irreducible ϖ) :
    (⋃ k : ℤ, genShell hϖ k) = {(0 : v.adicCompletion F)}ᶜ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [smul_eq_mul]
    exact mul_ne_zero (Units.ne_zero _) hy0
  · intro hx
    exact ⟨_, (mem_genShell_iff hϖ hx).mpr rfl⟩

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

theorem measurableSet_smul_set {c : v.adicCompletion F} (hc : c ≠ 0)
    {S : Set (v.adicCompletion F)} (hS : MeasurableSet S) :
    MeasurableSet (c • S) := by
  rw [smul_set_eq_preimage hc]
  exact hS.preimage (measurable_const_mul _)

theorem measurableSet_genShell (hϖ : Irreducible ϖ) (k : ℤ) :
    MeasurableSet (genShell hϖ k) :=
  measurableSet_smul_set (Units.ne_zero _) (measurableSet_shellSet hϖ 0)

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

omit [BorelSpace (v.adicCompletion F)] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulMeasure_eq_of_subset_smul_shell (hϖ : Irreducible ϖ)
    (w : (v.adicCompletion F)ˣ) {S : Set (v.adicCompletion F)} (hS : MeasurableSet S)
    (hsub : S ⊆ (w : v.adicCompletion F) • shellSet hϖ 0) :
    mulMeasure μ S = ((modulus (w : v.adicCompletion F) : ℝ≥0∞))⁻¹ * μ S := by
  have hmod : ∀ x ∈ S, modulus x = modulus (w : v.adicCompletion F) := by
    intro x hx
    rcases hsub hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    show modulus ((w : v.adicCompletion F) • y) = modulus (w : v.adicCompletion F)
    have hval : (w : v.adicCompletion F) • y
        = ((w * Units.mk0 y hy0 : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simp [smul_eq_mul]
    rw [hval, modulus_coe_units, map_mul]
    have h1 : distribHaarChar (v.adicCompletion F) (Units.mk0 y hy0) = 1 := by
      rw [LocalHaarModulus.distribHaarChar_adicCompletion,
        (mem_shellSet_iff_ord_eq hϖ 0 hy0).mp hy]
      simp
    rw [h1, mul_one, ← modulus_coe_units]
  have hS0 : S ⊆ {(0 : v.adicCompletion F)}ᶜ := by
    intro x hx
    rcases hsub hx with ⟨y, hy, rfl⟩
    have hy0 : y ≠ 0 := fun h => zero_notMem_shellSet hϖ 0 (h ▸ hy)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
    exact mul_ne_zero w.ne_zero hy0
  rw [mulMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr hS0,
    setLIntegral_congr_fun hS (fun x hx => by rw [hmod x hx]),
    setLIntegral_const]

theorem measure_units_smul (u : (v.adicCompletion F)ˣ) (S : Set (v.adicCompletion F)) :
    μ ((u : v.adicCompletion F) • S)
      = (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) * μ S := by
  rw [distribHaarChar_mul]
  rfl

theorem mulMeasure_units_smul (hϖ : Irreducible ϖ) (u : (v.adicCompletion F)ˣ)
    {T : Set (v.adicCompletion F)} (hT : MeasurableSet T)
    (hT0 : T ⊆ {(0 : v.adicCompletion F)}ᶜ) :
    mulMeasure μ ((u : v.adicCompletion F) • T) = mulMeasure μ T := by
  classical
  have hTdec : T = ⋃ k : ℤ, T ∩ genShell hϖ k := by
    rw [← Set.inter_iUnion, iUnion_genShell hϖ, Set.inter_eq_left.mpr hT0]
  have hmeasT : ∀ k : ℤ, MeasurableSet (T ∩ genShell hϖ k) :=
    fun k => hT.inter (measurableSet_genShell hϖ k)
  have hdisT : Pairwise (Function.onFun Disjoint (fun k => T ∩ genShell hϖ k)) :=
    fun _ _ hkl => ((genShell_disjoint hϖ hkl).mono inter_subset_right inter_subset_right)
  have hudec : (u : v.adicCompletion F) • T
      = ⋃ k : ℤ, (u : v.adicCompletion F) • (T ∩ genShell hϖ k) := by
    conv_lhs => rw [hTdec]
    rw [Set.smul_set_iUnion]
  have hmeasU : ∀ k : ℤ, MeasurableSet ((u : v.adicCompletion F) • (T ∩ genShell hϖ k)) :=
    fun k => measurableSet_smul_set u.ne_zero (hmeasT k)
  have hdisU : Pairwise
      (Function.onFun Disjoint (fun k => (u : v.adicCompletion F) • (T ∩ genShell hϖ k))) := by
    intro k l hkl
    rw [Function.onFun, smul_set_eq_preimage u.ne_zero, smul_set_eq_preimage u.ne_zero]
    exact (hdisT hkl).preimage _
  have hper : ∀ k : ℤ, mulMeasure μ ((u : v.adicCompletion F) • (T ∩ genShell hϖ k))
      = mulMeasure μ (T ∩ genShell hϖ k) := by
    intro k
    set w : (v.adicCompletion F)ˣ := piUnit hϖ ^ k with hw
    have hsub₁ : T ∩ genShell hϖ k ⊆ (w : v.adicCompletion F) • shellSet hϖ 0 :=
      fun x hx => hx.2
    have hsub₂ : (u : v.adicCompletion F) • (T ∩ genShell hϖ k)
        ⊆ ((u * w : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0 := by
      rintro x ⟨y, hy, rfl⟩
      rcases hsub₁ hy with ⟨z, hz, rfl⟩
      exact ⟨z, hz, by simp [smul_eq_mul, mul_assoc]⟩
    rw [mulMeasure_eq_of_subset_smul_shell μ hϖ (u * w) (hmeasU k) hsub₂,
      mulMeasure_eq_of_subset_smul_shell μ hϖ w (hmeasT k) hsub₁,
      measure_units_smul μ u]
    rw [modulus_coe_units, modulus_coe_units, map_mul]
    have hu0 : (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr distribHaarChar_pos.ne'
    have huT : (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hu0) (Or.inl huT)]
    calc (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)⁻¹
          * (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹
          * ((distribHaarChar (v.adicCompletion F) u : ℝ≥0∞) * μ (T ∩ genShell hϖ k))
        = (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹
          * ((distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)⁻¹
            * (distribHaarChar (v.adicCompletion F) u : ℝ≥0∞)) * μ (T ∩ genShell hϖ k) := by
          ring
      _ = (distribHaarChar (v.adicCompletion F) w : ℝ≥0∞)⁻¹ * μ (T ∩ genShell hϖ k) := by
          rw [ENNReal.inv_mul_cancel hu0 huT, mul_one]
  rw [hudec, measure_iUnion hdisU hmeasU]
  conv_rhs => rw [hTdec, measure_iUnion hdisT hmeasT]
  exact tsum_congr hper

variable [MeasurableSpace ((v.adicCompletion F)ˣ)] [BorelSpace ((v.adicCompletion F)ˣ)]

theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
  isOpenEmbedding_val.measurableEmbedding

def mulHaar : Measure (v.adicCompletion F)ˣ :=
  Measure.comap Units.val (mulMeasure μ)

omit [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulHaar_apply {A : Set (v.adicCompletion F)ˣ} (hA : MeasurableSet A) :
    mulHaar μ A = mulMeasure μ (Units.val '' A) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ hs => measurableEmbedding_val.measurableSet_image' hs) _ hA

theorem isMulLeftInvariant_mulHaar (hϖ : Irreducible ϖ) :
    (mulHaar μ).IsMulLeftInvariant := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  have hpre : (fun h => g * h) ⁻¹' A = g⁻¹ • A := by
    ext a
    simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hApre : MeasurableSet ((fun h => g * h) ⁻¹' A) :=
    hA.preimage (measurable_const_mul g)
  rw [hpre] at hApre ⊢
  rw [mulHaar_apply μ hApre, mulHaar_apply μ hA, image_val_smul]
  exact mulMeasure_units_smul μ hϖ g⁻¹ (measurableEmbedding_val.measurableSet_image' hA)
    (image_val_subset_compl_zero A)

theorem isFiniteMeasureOnCompacts_mulHaar (hϖ : Irreducible ϖ) :
    IsFiniteMeasureOnCompacts (mulHaar μ) := by
  haveI hT2 : T2Space ((v.adicCompletion F)ˣ) := Units.isEmbedding_val₀.t2Space
  constructor
  intro C hC
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  rw [mulHaar_apply μ hCm]
  have hC' : IsCompact (Units.val '' C) := hC.image Units.isEmbedding_val₀.continuous
  have hC'0 : (Units.val '' C) ⊆ {(0 : v.adicCompletion F)}ᶜ := image_val_subset_compl_zero C
  have hcov : (Units.val '' C) ⊆ ⋃ x : Units.val '' C,
      ((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2) : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) • shellSet hϖ 0 := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, 1, one_mem_shellSet_zero hϖ, ?_⟩
    simp [smul_eq_mul]
  have hopen : ∀ x : Units.val '' C, IsOpen
      (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2) : (v.adicCompletion F)ˣ)
        : v.adicCompletion F) • shellSet hϖ 0) :=
    fun _ => isOpen_smul_set (Units.ne_zero _) (isOpen_shellSet hϖ 0)
  obtain ⟨t, ht⟩ := hC'.elim_finite_subcover _ hopen hcov
  calc mulMeasure μ (Units.val '' C)
      ≤ mulMeasure μ (⋃ x ∈ t,
          (Units.val '' C) ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
            : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) := by
        refine measure_mono fun y hy => ?_
        rcases Set.mem_iUnion₂.mp (ht hy) with ⟨x, hxt, hyx⟩
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, hy, hyx⟩
    _ ≤ ∑ x ∈ t, mulMeasure μ ((Units.val '' C)
          ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
            : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) :=
        measure_biUnion_finset_le _ _
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.mpr fun x _ => ?_
        have hmeas : MeasurableSet ((Units.val '' C)
            ∩ (((Units.mk0 (x : v.adicCompletion F) (hC'0 x.2)
              : (v.adicCompletion F)ˣ) : v.adicCompletion F) • shellSet hϖ 0)) :=
          (hC'.isClosed.measurableSet).inter
            (measurableSet_smul_set (Units.ne_zero _) (measurableSet_shellSet hϖ 0))
        rw [mulMeasure_eq_of_subset_smul_shell μ hϖ _ hmeas inter_subset_right]
        refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ?_) ?_
        · rw [modulus_coe_units]
          exact ENNReal.coe_pos.mpr distribHaarChar_pos
        · refine lt_of_le_of_lt (measure_mono (inter_subset_right.trans
            (Set.smul_set_mono (shellSet_subset_integers hϖ 0)))) ?_
          rw [LocalHaarModulus.measure_smul_integers μ]
          exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_integers_lt_top μ)

omit [μ.Regular] in
theorem isOpenPosMeasure_mulHaar (hϖ : Irreducible ϖ) :
    (mulHaar μ).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  rw [mulHaar_apply μ hU.measurableSet]
  obtain ⟨u₀, hu₀⟩ := hUne
  have hUim : IsOpen (Units.val '' U) := isOpenEmbedding_val.isOpenMap _ hU
  have hWopen : IsOpen ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)) :=
    hUim.inter (isOpen_smul_set (Units.ne_zero _) (isOpen_shellSet hϖ 0))
  have hWne : ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)).Nonempty := by
    refine ⟨(u₀ : v.adicCompletion F), ⟨u₀, hu₀, rfl⟩, 1, one_mem_shellSet_zero hϖ, ?_⟩
    simp [smul_eq_mul]
  have hWpos : 0 < mulMeasure μ ((Units.val '' U)
      ∩ ((u₀ : v.adicCompletion F) • shellSet hϖ 0)) := by
    rw [mulMeasure_eq_of_subset_smul_shell μ hϖ u₀ hWopen.measurableSet inter_subset_right]
    refine ENNReal.mul_pos ?_ (hWopen.measure_pos μ hWne).ne'
    exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  exact (hWpos.trans_le (measure_mono inter_subset_left)).ne'

theorem isHaarMeasure_mulHaar (hϖ : Irreducible ϖ) : (mulHaar μ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_mulHaar μ hϖ
    toIsMulLeftInvariant := isMulLeftInvariant_mulHaar μ hϖ
    toIsOpenPosMeasure := isOpenPosMeasure_mulHaar μ hϖ }

end MulHaarFromAdditive
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_MulHaarFromAdditive
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_ArchMulHaarReal

set_option autoImplicit false

open MeasureTheory Set Filter Topology

open LanglandsTunnell.TateLocal

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_ArchMulHaarReal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_ArchMulHaarComplex

set_option autoImplicit false

open MeasureTheory Set

open LanglandsTunnell.TateLocal

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_ArchMulHaarComplex
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_ArchMulHaarCompletion

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell.TateLocal

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

omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem modulus_completion_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (a : w.Completion) : modulus a = ‖a‖₊ ^ d := by
  by_cases h : a = 0
  · subst h
    rw [modulus_zero, nnnorm_zero, zero_pow hd]
  · rw [modulus_of_ne_zero h, hΔ (Units.mk0 a h)]
    rfl

variable {μ : Measure w.Completion} [μ.IsAddHaarMeasure] [μ.Regular]

omit [BorelSpace w.Completion] [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulMeasure_completion_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    mulMeasure μ = (μ.restrict {0}ᶜ).withDensity fun x => ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ := by
  rw [mulMeasure]
  congr 1
  funext x
  rw [modulus_completion_eq w d hd hΔ]
  norm_cast

theorem measurable_nnnorm_pow_inv (d : ℕ) :
    Measurable fun x : w.Completion => ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ :=
  ((measurable_nnnorm.coe_nnreal_ennreal).pow_const d).inv

omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem units_smul_set_eq (t : (w.Completion)ˣ) (E : Set w.Completion) :
    (t • E : Set w.Completion) = (t : w.Completion) • E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem measure_units_smul (d : ℕ)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (t : (w.Completion)ˣ) (E : Set w.Completion) :
    μ ((t : w.Completion) • E) = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞) * μ E := by
  rw [← units_smul_set_eq, ← distribHaarChar_mul (μ := μ) t E, hΔ t]
  norm_cast

theorem map_units_smul (d : ℕ) (_hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (t : (w.Completion)ˣ) :
    Measure.map ((t : w.Completion) • ·) μ = ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞))⁻¹ • μ := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_const_smul _) hA, Measure.smul_apply, smul_eq_mul]
  have hpre : ((t : w.Completion) • ·) ⁻¹' A = ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • A := by
    ext x
    constructor
    · intro hx
      refine ⟨(t : w.Completion) • x, hx, ?_⟩
      show ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • (t : w.Completion) • x = x
      rw [smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero t), one_smul]
    · rintro ⟨y, hy, rfl⟩
      show (t : w.Completion) • ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • y ∈ A
      rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero t), one_smul]
      exact hy
  rw [hpre, measure_units_smul w d hΔ t⁻¹ A]
  congr 1
  rw [Units.val_inv_eq_inv_val, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr (Units.ne_zero t)),
    ← ENNReal.inv_pow]

omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem smul_set_subset_compl_zero (t : (w.Completion)ˣ) {E : Set w.Completion}
    (hE0 : E ⊆ {0}ᶜ) : (t : w.Completion) • E ⊆ ({0}ᶜ : Set w.Completion) := by
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
  exact mul_ne_zero (Units.ne_zero t) (fun h => hE0 hy (by simp [h]))

theorem measurableSet_units_smul (t : (w.Completion)ˣ) {E : Set w.Completion}
    (hE : MeasurableSet E) : MeasurableSet ((t : w.Completion) • E) := by
  have h : (t : w.Completion) • E
      = (fun x => ((t⁻¹ : (w.Completion)ˣ) : w.Completion) * x) ⁻¹' E := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (Units.ne_zero t), Set.mem_preimage]
    rw [Units.val_inv_eq_inv_val]
    rfl
  rw [h]
  exact hE.preimage (measurable_const_mul _)

theorem mulMeasure_units_smul (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    (t : (w.Completion)ˣ) {E : Set w.Completion}
    (hE : MeasurableSet E) (hE0 : E ⊆ {0}ᶜ) :
    mulMeasure μ ((t : w.Completion) • E) = mulMeasure μ E := by
  have hne : ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)) ≠ 0 :=
    pow_ne_zero d (ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr (Units.ne_zero t)))
  have hnt : ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcE : MeasurableSet ((t : w.Completion) • E) := measurableSet_units_smul w t hE
  rw [mulMeasure_completion_eq w d hd hΔ, withDensity_apply _ hcE, withDensity_apply _ hE,
    Measure.restrict_restrict hcE, Measure.restrict_restrict hE,
    Set.inter_eq_left.mpr (smul_set_subset_compl_zero w t hE0), Set.inter_eq_left.mpr hE0]
  have hμ : μ = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞) • Measure.map ((t : w.Completion) • ·) μ := by
    rw [map_units_smul w d hd hΔ t, smul_smul, ENNReal.mul_inv_cancel hne hnt, one_smul]
  have hpre : ((t : w.Completion) • ·) ⁻¹' ((t : w.Completion) • E) = E := by
    ext x
    simp only [Set.mem_preimage]
    exact Set.smul_mem_smul_set_iff₀ (Units.ne_zero t) E x
  calc ∫⁻ x in (t : w.Completion) • E, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ
      = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)
          * ∫⁻ x in (t : w.Completion) • E, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹
              ∂(Measure.map ((t : w.Completion) • ·) μ) := by
        conv_lhs => rw [hμ]
        rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = (‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞)
          * ∫⁻ y in E, ((‖(t : w.Completion) • y‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
        rw [setLIntegral_map hcE (measurable_nnnorm_pow_inv w d) (measurable_const_smul _), hpre]
    _ = ∫⁻ y in E, ((‖y‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
        have hint : ∀ y : w.Completion, (((‖(t : w.Completion) • y‖₊ ^ d : ℝ≥0∞)))⁻¹
            = ((‖(t : w.Completion)‖₊ ^ d : ℝ≥0∞))⁻¹ * ((‖y‖₊ ^ d : ℝ≥0∞))⁻¹ := by
          intro y
          rw [smul_eq_mul, nnnorm_mul, ENNReal.coe_mul, mul_pow]
          exact ENNReal.mul_inv (Or.inl hne) (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))
        simp only [hint]
        rw [lintegral_const_mul _ (measurable_nnnorm_pow_inv w d), ← mul_assoc,
          ENNReal.mul_inv_cancel hne hnt, one_mul]

omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem isOpenEmbedding_val_completion :
    Topology.IsOpenEmbedding (Units.val : (w.Completion)ˣ → w.Completion) :=
  Units.isOpenEmbedding_val

omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem image_val_subset_compl_zero (A : Set (w.Completion)ˣ) :
    (Units.val '' A : Set w.Completion) ⊆ {0}ᶜ := by
  rintro x ⟨u, _, rfl⟩
  exact u.ne_zero

omit [MeasurableSpace w.Completion] [BorelSpace w.Completion] in
theorem image_val_preimage_mul (t : (w.Completion)ˣ) (A : Set (w.Completion)ˣ) :
    (Units.val '' ((fun u => t * u) ⁻¹' A) : Set w.Completion)
      = ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨((t * u : (w.Completion)ˣ) : w.Completion), ⟨t * u, hu, rfl⟩, ?_⟩
    show ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • ((t * u : (w.Completion)ˣ) : w.Completion)
        = (u : w.Completion)
    rw [smul_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val, ← mul_assoc,
      inv_mul_cancel₀ (Units.ne_zero t), one_mul]
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨t⁻¹ * v, by simpa using hv, ?_⟩
    show ((t⁻¹ * v : (w.Completion)ˣ) : w.Completion)
        = ((t⁻¹ : (w.Completion)ˣ) : w.Completion) • (v : w.Completion)
    rw [Units.val_mul, smul_eq_mul]

variable [MeasurableSpace (w.Completion)ˣ] [BorelSpace (w.Completion)ˣ]

theorem measurableEmbedding_val_completion :
    MeasurableEmbedding (Units.val : (w.Completion)ˣ → w.Completion) :=
  (isOpenEmbedding_val_completion w).measurableEmbedding

def mulHaarCompletion (μ : Measure w.Completion) : Measure (w.Completion)ˣ :=
  Measure.comap Units.val (mulMeasure μ)

omit [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulHaarCompletion_apply {A : Set (w.Completion)ˣ} (hA : MeasurableSet A) :
    mulHaarCompletion w μ A = mulMeasure μ (Units.val '' A) :=
  Measure.comap_apply _ (fun _ _ h => Units.ext h)
    (fun _ hs => (measurableEmbedding_val_completion w).measurableSet_image' hs) _ hA

theorem isMulLeftInvariant_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    (mulHaarCompletion w μ).IsMulLeftInvariant := by
  refine ⟨fun t => ?_⟩
  refine Measure.ext fun A hA => ?_
  have hmt : Measurable fun u : (w.Completion)ˣ => t * u :=
    (Homeomorph.mulLeft t).continuous.measurable
  rw [Measure.map_apply hmt hA]
  have hpre : MeasurableSet ((fun u => t * u) ⁻¹' A) := hA.preimage hmt
  rw [mulHaarCompletion_apply w hpre, mulHaarCompletion_apply w hA, image_val_preimage_mul]
  exact mulMeasure_units_smul w d hd hΔ t⁻¹
    ((measurableEmbedding_val_completion w).measurableSet_image' hA)
    (image_val_subset_compl_zero w A)

omit [μ.IsAddHaarMeasure] [μ.Regular] in
theorem mulMeasure_image_val_eq (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d)
    {A : Set (w.Completion)ˣ} (hA : MeasurableSet A) :
    mulMeasure μ (Units.val '' A)
      = ∫⁻ x in (Units.val '' A), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
  have hAm : MeasurableSet (Units.val '' A : Set w.Completion) :=
    (measurableEmbedding_val_completion w).measurableSet_image' hA
  rw [mulMeasure_completion_eq w d hd hΔ, withDensity_apply _ hAm, Measure.restrict_restrict hAm,
    Set.inter_eq_left.mpr (image_val_subset_compl_zero w A)]

omit [μ.Regular] in
theorem isFiniteMeasureOnCompacts_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    IsFiniteMeasureOnCompacts (mulHaarCompletion w μ) := by
  refine ⟨fun K hK => ?_⟩
  rw [mulHaarCompletion_apply w hK.measurableSet, mulMeasure_image_val_eq w d hd hΔ hK.measurableSet]
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hKc : IsCompact (Units.val '' K : Set w.Completion) :=
    hK.image (isOpenEmbedding_val_completion w).continuous
  obtain ⟨x₀, hx₀K, hx₀min⟩ :=
    hKc.exists_isMinOn (hne.image _) continuous_norm.continuousOn
  have hx₀0 : x₀ ≠ 0 := image_val_subset_compl_zero w K hx₀K
  have hb : ∀ x ∈ (Units.val '' K : Set w.Completion),
      ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ≤ ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr ?_
    have : ‖x₀‖₊ ≤ ‖x‖₊ := by exact_mod_cast (isMinOn_iff.mp hx₀min) x hx
    exact_mod_cast pow_le_pow_left' this d
  calc ∫⁻ x in (Units.val '' K), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ
      ≤ ∫⁻ _ in (Units.val '' K), ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ :=
        setLIntegral_mono' hKc.measurableSet hb
    _ = ((‖x₀‖₊ ^ d : ℝ≥0∞))⁻¹ * μ (Units.val '' K) := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.mpr (ENNReal.pow_pos (ENNReal.coe_pos.mpr (nnnorm_pos.mpr hx₀0)) d))
        hKc.measure_lt_top

omit [μ.Regular] in
theorem isOpenPosMeasure_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    (mulHaarCompletion w μ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [mulHaarCompletion_apply w hU.measurableSet, mulMeasure_image_val_eq w d hd hΔ hU.measurableSet]
  obtain ⟨u, hu⟩ := hne
  set W : Set w.Completion := (Units.val '' U)
      ∩ Metric.ball ((u : (w.Completion)ˣ) : w.Completion) (‖((u : (w.Completion)ˣ) : w.Completion)‖ / 2)
    with hW
  have hWo : IsOpen W :=
    ((isOpenEmbedding_val_completion w).isOpenMap _ hU).inter Metric.isOpen_ball
  have hWne : W.Nonempty :=
    ⟨(u : w.Completion), ⟨u, hu, rfl⟩,
      Metric.mem_ball_self (half_pos (norm_pos_iff.mpr (Units.ne_zero u)))⟩
  have hbound : ∀ x ∈ W,
      ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹
        ≤ ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ := by
    intro x hx
    refine ENNReal.inv_le_inv.mpr ?_
    have hxb : ‖x‖₊ ≤ ‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2 := by
      have hdist := Metric.mem_ball.mp hx.2
      rw [dist_eq_norm] at hdist
      have : ‖x‖ ≤ ‖((u : (w.Completion)ˣ) : w.Completion)‖ * 2 := by
        have h1 := norm_le_norm_add_norm_sub' x ((u : (w.Completion)ˣ) : w.Completion)
        nlinarith [norm_nonneg ((u : (w.Completion)ˣ) : w.Completion),
          norm_nonneg (x - ((u : (w.Completion)ˣ) : w.Completion))]
      exact_mod_cast this
    calc ((‖x‖₊ ^ d : ℝ≥0) : ℝ≥0∞)
        ≤ (((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast pow_le_pow_left' hxb d
      _ = ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞))) := by push_cast; ring
  have hpos : (0 : ℝ≥0∞) < ∫⁻ x in (Units.val '' U), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := by
    calc (0 : ℝ≥0∞)
        < ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹ * μ W := by
          refine ENNReal.mul_pos ?_ (hWo.measure_pos μ hWne).ne'
          exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top (ENNReal.mul_ne_top
            ENNReal.coe_ne_top (by simp)))
      _ = ∫⁻ _ in W, ((((‖((u : (w.Completion)ˣ) : w.Completion)‖₊ * 2) ^ d : ℝ≥0∞)))⁻¹ ∂μ :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in W, ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ := setLIntegral_mono' hWo.measurableSet hbound
      _ ≤ ∫⁻ x in (Units.val '' U), ((‖x‖₊ ^ d : ℝ≥0∞))⁻¹ ∂μ :=
          lintegral_mono_set Set.inter_subset_left
  exact hpos.ne'

theorem isHaarMeasure_mulHaarCompletion (d : ℕ) (hd : d ≠ 0)
    (hΔ : ∀ t : (w.Completion)ˣ, distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ d) :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := isFiniteMeasureOnCompacts_mulHaarCompletion w d hd hΔ
    toIsMulLeftInvariant := isMulLeftInvariant_mulHaarCompletion w d hd hΔ
    toIsOpenPosMeasure := isOpenPosMeasure_mulHaarCompletion w d hd hΔ }

theorem isHaarMeasure_mulHaarCompletion_of_isReal (hv : w.IsReal) :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  isHaarMeasure_mulHaarCompletion w 1 one_ne_zero
    (distribHaarChar_completion_of_isReal w hv)

theorem isHaarMeasure_mulHaarCompletion_of_isComplex (hv : w.IsComplex) :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  isHaarMeasure_mulHaarCompletion w 2 two_ne_zero
    (distribHaarChar_completion_of_isComplex w hv)

theorem isHaarMeasure_mulHaarCompletion_total :
    (mulHaarCompletion w μ).IsHaarMeasure :=
  (w.isReal_or_isComplex).elim
    (isHaarMeasure_mulHaarCompletion_of_isReal w)
    (isHaarMeasure_mulHaarCompletion_of_isComplex w)

end ArchMulHaarCompletion
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_ArchMulHaarCompletion
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_ValuedOrdBridge

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_ValuedOrdBridge
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_TateReference

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set"

open M4aLocalCFT LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

section RangeVal

variable {K : Type*} [GroupWithZero K]

theorem range_units_val : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

end RangeVal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section CompVal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

theorem mulMeasure_singleton_zero (μ : Measure K) : mulMeasure μ {0} = 0 := by
  rw [mulMeasure, withDensity_apply _ (measurableSet_singleton 0),
    Measure.restrict_restrict (measurableSet_singleton 0), Set.inter_compl_self, Measure.restrict_empty,
    lintegral_zero_measure]

theorem mulMeasure_restrict_compl_zero (μ : Measure K) : (mulMeasure μ).restrict {0}ᶜ = mulMeasure μ := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  have h : {a : K | ¬a ∈ ({0}ᶜ : Set K)} = {0} := by
    ext a
    simp
  rw [h]
  exact mulMeasure_singleton_zero μ

variable [MeasurableSpace Kˣ]

theorem integral_comp_val_comap_mulMeasure (hval : MeasurableEmbedding (Units.val : Kˣ → K)) (μ : Measure K)
    (φ : K → ℂ) : ∫ t, φ (t : K) ∂(Measure.comap Units.val (mulMeasure μ)) = ∫ x, φ x ∂(mulMeasure μ) := by
  rw [← hval.integral_map, hval.map_comap, range_units_val, mulMeasure_restrict_compl_zero]

theorem localZeta_eq_integral_comap (hval : MeasurableEmbedding (Units.val : Kˣ → K)) (μ : Measure K)
    (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta μ f χ s
      = ∫ t, f t * (χ t : ℂ) * ((modulus (t : K) : ℝ) : ℂ) ^ s ∂(Measure.comap Units.val (mulMeasure μ)) := by
  have h := integral_comp_val_comap_mulMeasure hval μ (fun x => f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s)
  simp only [charExt_coe_units] at h
  rw [localZeta, ← h]

end CompVal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] countable_heightOneSpectrum

section Instances

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instLocallyCompactSpaceArchUnits : LocallyCompactSpace (InfiniteAdeleRing F)ˣ := inferInstance

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instLocallyCompactSpaceSUnitsProdDeepUnits :
    LocallyCompactSpace (SUnits (F := F) S × DeepUnits (F := F) S) := inferInstance

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instLocallyCompactSpaceQ : LocallyCompactSpace (Q (F := F) S) := inferInstance

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

scoped instance instBorelSpaceDeepUnits : BorelSpace (DeepUnits (F := F) S) := Pi.borelSpace

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

scoped instance instBorelSpaceSUnitsProdDeepUnits : BorelSpace (SUnits (F := F) S × DeepUnits (F := F) S) :=
  Prod.borelSpace

scoped instance instMeasurableMulSUnitsProdDeepUnits : MeasurableMul (SUnits (F := F) S × DeepUnits (F := F) S) :=
  inferInstance

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

scoped instance instBorelSpaceQ : BorelSpace (Q (F := F) S) := Prod.borelSpace

scoped instance instMeasurableMulArchUnits : MeasurableMul (InfiniteAdeleRing F)ˣ := inferInstance

end Instances
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Deep

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

def deepRef : Measure (DeepUnits (F := F) S) := haarMeasure ⊤

scoped instance isHaarMeasure_deepRef : (deepRef (F := F) S).IsHaarMeasure := by
  unfold deepRef
  infer_instance

theorem deepRef_univ : deepRef (F := F) S Set.univ = 1 := by
  rw [deepRef, ← PositiveCompacts.coe_top]
  exact haarMeasure_self

scoped instance isProbabilityMeasure_deepRef : IsProbabilityMeasure (deepRef (F := F) S) :=
  ⟨deepRef_univ S⟩

end Deep
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section SFactor

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

scoped instance instIsHaarMeasureMulHaar (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] : (MulHaarFromAdditive.mulHaar μ).IsHaarMeasure := by
  obtain ⟨ϖ, hϖ, -⟩ := ValuedOrdBridge.exists_irreducible_valued (v := v)
  exact MulHaarFromAdditive.isHaarMeasure_mulHaar μ hϖ

def sRef (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) : Measure (SUnits (F := F) S) :=
  Measure.pi fun v : S => MulHaarFromAdditive.mulHaar (μf v.1)

scoped instance isHaarMeasure_sRef (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure] : (sRef S μf).IsHaarMeasure := by
  unfold sRef
  infer_instance

scoped instance sigmaFinite_sRef (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure] : SigmaFinite (sRef S μf) := by
  unfold sRef
  infer_instance

theorem localZeta_eq_integral_mulHaar {v : HeightOneSpectrum (𝓞 F)} (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) :
    localZeta μ f χ s = ∫ t, f t * (χ t : ℂ) * ((modulus (t : v.adicCompletion F) : ℝ) : ℂ) ^ s
      ∂(MulHaarFromAdditive.mulHaar μ) :=
  localZeta_eq_integral_comap MulHaarFromAdditive.measurableEmbedding_val μ f χ s

end SFactor
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Arch

def archPiUnits : (InfiniteAdeleRing F)ˣ ≃ₜ* ((w : InfinitePlace F) → (w.Completion)ˣ) :=
  ContinuousMulEquiv.piUnits

omit [NumberField F] in
theorem archPiUnits_apply (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    ((archPiUnits a w : (w.Completion)ˣ) : w.Completion) = (a : InfiniteAdeleRing F) w := rfl

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]

scoped instance instIsHaarMeasureMulHaarCompletion (w : InfinitePlace F) (μ : Measure w.Completion)
    [μ.IsAddHaarMeasure] : (ArchMulHaarCompletion.mulHaarCompletion w μ).IsHaarMeasure :=
  ArchMulHaarCompletion.isHaarMeasure_mulHaarCompletion_total w

omit [NumberField F] in
theorem localZeta_eq_integral_mulHaarCompletion (w : InfinitePlace F) (μ : Measure w.Completion)
    (f : w.Completion → ℂ) (χ : (w.Completion)ˣ →* ℂˣ) (s : ℂ) :
    localZeta μ f χ s = ∫ t, f t * (χ t : ℂ) * ((modulus (t : w.Completion) : ℝ) : ℂ) ^ s
      ∂(ArchMulHaarCompletion.mulHaarCompletion w μ) :=
  localZeta_eq_integral_comap (ArchMulHaarCompletion.measurableEmbedding_val_completion w) μ f χ s

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

def archRef (μa : (w : InfinitePlace F) → Measure (w.Completion)) : Measure (InfiniteAdeleRing F)ˣ :=
  (Measure.pi fun w : InfinitePlace F => ArchMulHaarCompletion.mulHaarCompletion w (μa w)).map
    (archPiUnits (F := F)).symm

scoped instance isHaarMeasure_archRef (μa : (w : InfinitePlace F) → Measure (w.Completion))
    [∀ w, (μa w).IsAddHaarMeasure] : (archRef μa).IsHaarMeasure := by
  unfold archRef
  infer_instance

scoped instance sigmaFinite_archRef (μa : (w : InfinitePlace F) → Measure (w.Completion))
    [∀ w, (μa w).IsAddHaarMeasure] : SigmaFinite (archRef μa) :=
  inferInstance

omit [∀ w : InfinitePlace F, BorelSpace (w.Completion)] in
theorem integral_archRef (μa : (w : InfinitePlace F) → Measure (w.Completion)) (G : (InfiniteAdeleRing F)ˣ → ℂ) :
    ∫ a, G a ∂(archRef μa)
      = ∫ t, G ((archPiUnits (F := F)).symm t)
          ∂(Measure.pi fun w : InfinitePlace F => ArchMulHaarCompletion.mulHaarCompletion w (μa w)) := by
  unfold archRef
  exact (archPiUnits (F := F)).symm.toHomeomorph.measurableEmbedding.integral_map G

end Arch
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

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

def refMeasure : Measure (Q (F := F) S) := (archRef μa).prod ((sRef S μf).prod (deepRef S))

set_option synthInstance.maxHeartbeats 800000 in
scoped instance isHaarMeasure_refMeasure : (refMeasure S μa μf).IsHaarMeasure := by
  unfold refMeasure
  infer_instance

theorem integral_refMeasure_mul (A : (InfiniteAdeleRing F)ˣ → ℂ) (B : SUnits (F := F) S → ℂ)
    (C : DeepUnits (F := F) S → ℂ) :
    ∫ q, A q.1 * (B q.2.1 * C q.2.2) ∂(refMeasure S μa μf)
      = (∫ a, A a ∂(archRef μa)) * ((∫ t, B t ∂(sRef S μf)) * ∫ o, C o ∂(deepRef S)) := by
  unfold refMeasure
  rw [integral_prod_mul (μ := archRef μa) A (fun p : SUnits (F := F) S × DeepUnits (F := F) S => B p.1 * C p.2),
    integral_prod_mul]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

def refConst : ℝ≥0 := haarScalarFactor (asmMeasure S ν) (refMeasure S μa μf)

theorem refConst_pos : 0 < refConst S μa μf ν :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

theorem asmMeasure_eq_refConst_smul : asmMeasure S ν = refConst S μa μf ν • refMeasure S μa μf :=
  isMulLeftInvariant_eq_smul _ _

theorem integral_asmMeasure_eq_refConst_mul (G : Q (F := F) S → ℂ) :
    ∫ q, G q ∂(asmMeasure S ν) = ((refConst S μa μf ν : ℝ) : ℂ) * ∫ q, G q ∂(refMeasure S μa μf) := by
  rw [asmMeasure_eq_refConst_smul S μa μf ν, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem setIntegral_unitsOutside_eq_refConst_mul (G : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    ∫ x in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), G x ∂ν
      = ((refConst S μa μf ν : ℝ) : ℂ) * ∫ q, G (asm S q) ∂(refMeasure S μa μf) := by
  rw [setIntegral_unitsOutside_eq_integral_asmMeasure, integral_asmMeasure_eq_refConst_mul S μa μf ν]

end Reference
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Factorwise

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

section DeepConst

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

theorem integral_deepRef_const (c : ℂ) : ∫ _o, c ∂(deepRef (F := F) S) = c := by
  rw [integral_const, probReal_univ, one_smul]

end DeepConst
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section SProd

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

theorem integral_sRef_prod (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure] (φ : (v : S) → (v.1.adicCompletion F)ˣ → ℂ) :
    ∫ t, ∏ v : S, φ v (t v) ∂(sRef S μf) = ∏ v : S, ∫ u, φ v u ∂(MulHaarFromAdditive.mulHaar (μf v.1)) :=
  integral_fintype_prod_eq_prod φ

end SProd
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section ArchProd

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

theorem integral_archRef_prod (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (φ : (w : InfinitePlace F) → (w.Completion)ˣ → ℂ) :
    ∫ a, ∏ w, φ w (archPiUnits a w) ∂(archRef μa)
      = ∏ w, ∫ t, φ w t ∂(ArchMulHaarCompletion.mulHaarCompletion w (μa w)) := by
  rw [integral_archRef]
  simp only [ContinuousMulEquiv.apply_symm_apply]
  exact integral_fintype_prod_eq_prod φ

end ArchProd
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Factorwise
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_TateReference
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_LocalGlobalModulus

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_LocalGlobalModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_ArchLocalGlobalModulus

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel NumberField.AdelicVolume IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

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
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_ArchLocalGlobalModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_TateFubini

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter"

open M4aLocalCFT LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
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

theorem char_asm (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (q : Q (F := F) S) :
    χ (asm S q) = (∏ w, archLocalChar χ w (archPiUnits q.1 w))
      * ((∏ v : S, localChar χ v.1 (q.2.1 v)) * χ (deepAsm S q.2.2)) := by
  rw [asm_apply, map_mul, map_mul, archAsm_eq_prod_archUnitHom, map_prod, sAsm_apply, map_prod]
  rfl

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

theorem asm_val_fst_apply (q : Q (F := F) S) (w : InfinitePlace F) :
    ((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = ((archPiUnits q.1 w : (w.Completion)ˣ) : w.Completion) :=
  congrArg (fun u : (InfiniteAdeleRing F)ˣ => (u : InfiniteAdeleRing F) w) (archUnits_asm S q)

theorem asm_val_snd_apply_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((q.2.1 ⟨v, hv⟩ : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
  congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) (unitAtHom_asm_of_mem S q hv)

theorem asm_val_mem_integralOutside (q : Q (F := F) S) :
    ((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S :=
  ((mem_unitsOutside_iff S _).mp (asm_mem_unitsOutside S q)).1

theorem apply_asm_of_isFactorizableStandardOutside {f : AdeleRing (𝓞 F) F → ℂ}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (q : Q (F := F) S) :
    f (asm S q) = (∏ w, g w (archPiUnits q.1 w)) * ∏ v : S, h v.1 (q.2.1 v) := by
  rw [hf, Set.indicator_of_mem (asm_val_mem_integralOutside S q)]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by rw [asm_val_fst_apply]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [asm_val_snd_apply_of_mem S q v.2]

end AlongAsm
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

theorem cpow_prod_ofReal_nonneg {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (z : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z := by
  classical
  refine @Finset.induction_on ι (fun s => (∀ i ∈ s, 0 ≤ r i) →
      (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z) _ s (fun _ => by simp) ?_ hr
  intro a s ha ih hr
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (hr a (Finset.mem_insert_self a s))
      (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)) z,
    ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

section DeepTrivial

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

open scoped Classical in
def truncDeep (T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) (o : DeepUnits (F := F) S) :
    DeepUnits (F := F) S :=
  fun v => if v ∈ T then o v else 1

theorem truncDeep_empty (o : DeepUnits (F := F) S) : truncDeep S ∅ o = 1 := by
  funext v
  simp [truncDeep]

open scoped Classical in
theorem truncDeep_insert {T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S}}
    {v₀ : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}} (hv₀ : v₀ ∉ T) (o : DeepUnits (F := F) S) :
    truncDeep S (insert v₀ T) o = Pi.mulSingle v₀ (o v₀) * truncDeep S T o := by
  funext v
  simp only [truncDeep, Pi.mul_apply, Finset.mem_insert]
  by_cases h : v = v₀
  · subst h
    rw [Pi.mulSingle_eq_same, if_pos (Or.inl rfl), if_neg hv₀, mul_one]
  · rw [Pi.mulSingle_eq_of_ne h, one_mul]
    by_cases hT : v ∈ T
    · rw [if_pos (Or.inr hT), if_pos hT]
    · rw [if_neg (not_or.mpr ⟨h, hT⟩), if_neg hT]

open scoped Classical in
theorem tendsto_truncDeep (o : DeepUnits (F := F) S) : Tendsto (fun T => truncDeep S T o) atTop (𝓝 o) := by
  refine tendsto_pi_nhds.mpr fun v => ?_
  refine (tendsto_const_nhds (x := o v)).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ({v} : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S})] with T hT
  show o v = truncDeep S T o v
  simp only [truncDeep]
  rw [if_pos (Finset.singleton_subset_iff.mp hT)]

theorem coe_unitsMap_integers_mem {v : HeightOneSpectrum (𝓞 F)} (u : (v.adicCompletionIntegers F)ˣ) :
    ((Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      ∈ v.adicCompletionIntegers F :=
  (u : v.adicCompletionIntegers F).2

theorem coe_unitsMap_integers_inv_mem {v : HeightOneSpectrum (𝓞 F)} (u : (v.adicCompletionIntegers F)ˣ) :
    (((Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u : (v.adicCompletion F)ˣ)⁻¹
        : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  rw [← map_inv]
  exact ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2

open scoped Classical in
theorem deepAsm_mulSingle {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (u : (v.adicCompletionIntegers F)ˣ) :
    deepAsm S (Pi.mulSingle (⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) u)
      = embUnit v (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) := by
  refine idele_ext ?_ (fun w => ?_)
  · rw [archUnits_deepAsm]
    exact (Units.ext (embUnit_val_fst v (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u))).symm
  · by_cases hw : w ∈ S
    · rw [unitAtHom_deepAsm_of_mem S _ hw, unitAtHom_embUnit_of_ne]
      exact fun h => hv (h ▸ hw)
    · rw [unitAtHom_deepAsm_of_not_mem S _ hw]
      by_cases hwv : w = v
      · subst hwv
        rw [Pi.mulSingle_eq_same, unitAtHom_embUnit_self]
      · rw [Pi.mulSingle_eq_of_ne (fun h => hwv (congrArg Subtype.val h)), map_one, unitAtHom_embUnit_of_ne hwv]

open scoped Classical in
theorem char_deepAsm_truncDeep (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v)
    (T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) (o : DeepUnits (F := F) S) :
    χ (deepAsm S (truncDeep S T o)) = 1 := by
  induction T using Finset.induction_on with
  | empty => rw [truncDeep_empty, map_one, map_one]
  | @insert v₀ T hv₀ ih =>
    rw [truncDeep_insert S hv₀, map_mul, map_mul, ih, mul_one]
    obtain ⟨v, hv⟩ := v₀
    rw [deepAsm_mulSingle S hv]
    exact hχS v hv _ (coe_unitsMap_integers_mem _) (coe_unitsMap_integers_inv_mem _)

theorem char_deepAsm_eq_one (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (o : DeepUnits (F := F) S) : χ (deepAsm S o) = 1 := by
  have hcont : Continuous fun o : DeepUnits (F := F) S => χ (deepAsm S o) :=
    hχc.comp (continuous_deepAsm S)
  have h1 : Tendsto (fun T => χ (deepAsm S (truncDeep S T o))) atTop (𝓝 (χ (deepAsm S o))) :=
    (hcont.tendsto o).comp (tendsto_truncDeep S o)
  have h2 : Tendsto (fun T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => χ (deepAsm S (truncDeep S T o)))
      atTop (𝓝 1) := by
    simp_rw [char_deepAsm_truncDeep S χ hχS]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end DeepTrivial
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Integrands

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def archLocalIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (w : InfinitePlace F) (u : (w.Completion)ˣ) : ℂ :=
  g w u * (archLocalChar χ w u : ℂ) * (((distribHaarChar (w.Completion) u : ℝ≥0) : ℝ) : ℂ) ^ s

def finLocalIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) : ℂ :=
  h v u * (localChar χ v u : ℂ) * (((distribHaarChar (v.adicCompletion F) u : ℝ≥0) : ℝ) : ℂ) ^ s

def archIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (a : (InfiniteAdeleRing F)ˣ) : ℂ :=
  ∏ w, archLocalIntegrand g χ s w (archPiUnits a w)

def sIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (s : ℂ) (t : SUnits (F := F) S) : ℂ :=
  ∏ v : S, finLocalIntegrand h χ s v.1 (t v)

theorem zetaIntegrand_asm {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
    {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ} (hf : IsFactorizableStandardOutside f S g h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ)
    (q : Q (F := F) S) :
    f (asm S q) * ((χ (asm S q) : ℂˣ) : ℂ) * ((ideleNorm F (asm S q) : ℝ) : ℂ) ^ s
      = archIntegrand g χ s q.1 * (sIntegrand S h χ s q.2.1 * (1 : DeepUnits (F := F) S → ℂ) q.2.2) := by
  rw [apply_asm_of_isFactorizableStandardOutside S hf, char_asm S χ, char_deepAsm_eq_one S χ hχc hχS, mul_one,
    ideleNorm_asm S, Units.val_mul, Units.coe_prod, Units.coe_prod, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun w _ => NNReal.coe_nonneg _)
      (Finset.prod_nonneg fun v _ => NNReal.coe_nonneg _),
    cpow_prod_ofReal_nonneg _ _ (fun w _ => NNReal.coe_nonneg _),
    cpow_prod_ofReal_nonneg _ _ (fun v _ => NNReal.coe_nonneg _),
    Pi.one_apply, mul_one]
  unfold archIntegrand sIntegrand archLocalIntegrand finLocalIntegrand
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end Integrands
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section LocalIntegrals

section ArchLocal

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion))

theorem integral_archLocalIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (w : InfinitePlace F) :
    ∫ u, archLocalIntegrand g χ s w u ∂(ArchMulHaarCompletion.mulHaarCompletion w (μa w))
      = localZeta (μa w) (g w) (archLocalChar χ w) s := by
  rw [localZeta_eq_integral_mulHaarCompletion]
  simp_rw [modulus_coe_units]
  rfl

end ArchLocal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section FinLocal

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))

theorem integral_finLocalIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ∫ u, finLocalIntegrand h χ s v u ∂(MulHaarFromAdditive.mulHaar (μf v))
      = localZeta (μf v) (h v) (localChar χ v) s := by
  rw [localZeta_eq_integral_mulHaar]
  simp_rw [modulus_coe_units]
  rfl

end FinLocal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end LocalIntegrals
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

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

theorem setIntegral_unitsOutside_zetaIntegrand_eq {f : AdeleRing (𝓞 F) F → ℂ}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) :
    ∫ x in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν
      = ((refConst S μa μf ν : ℝ) : ℂ)
          * ((∏ w, localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, localZeta (μf v) (h v) (localChar χ v) s) := by
  rw [setIntegral_unitsOutside_eq_refConst_mul S μa μf ν]
  congr 1
  have hpt : (fun q : Q (F := F) S =>
        f (asm S q) * ((χ (asm S q) : ℂˣ) : ℂ) * ((ideleNorm F (asm S q) : ℝ) : ℂ) ^ s)
      = fun q => archIntegrand g χ s q.1 * (sIntegrand S h χ s q.2.1 * (1 : DeepUnits (F := F) S → ℂ) q.2.2) :=
    funext fun q => zetaIntegrand_asm S hf χ hχc hχS s q
  rw [hpt, integral_refMeasure_mul S μa μf (archIntegrand g χ s) (sIntegrand S h χ s) 1]
  simp only [Pi.one_apply, integral_deepRef_const, mul_one]
  unfold archIntegrand sIntegrand
  rw [integral_archRef_prod μa (archLocalIntegrand g χ s),
    integral_sRef_prod S μf (fun v => finLocalIntegrand h χ s v.1)]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => integral_archLocalIntegrand μa g χ s w
  · calc ∏ v : S, ∫ u, finLocalIntegrand h χ s v.1 u ∂(MulHaarFromAdditive.mulHaar (μf v.1))
        = ∏ v : S, localZeta (μf v.1) (h v.1) (localChar χ v.1) s :=
          Finset.prod_congr rfl fun v _ => integral_finLocalIntegrand μf h χ s v.1
      _ = ∏ v ∈ S, localZeta (μf v) (h v) (localChar χ v) s :=
          Finset.prod_coe_sort S fun v => localZeta (μf v) (h v) (localChar χ v) s

end Master
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_TateFubini
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_TateSDecomp4

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory Set"

open scoped NNReal Pointwise

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in
theorem ordAt_nonneg_of_mem (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    (ht : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F) : 0 ≤ ordAt v t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have ha : (⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    exact t.ne_zero (congrArg Subtype.val h)
  have hbot : Ideal.span {(⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
  have hspan : Ideal.span {(⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F)}
      = IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have h := M4aLocalCFT.ValuationOrd.ord_ofMul_of_mem (v.adicCompletionIntegers F) ht hspan
  rw [ordAt, h]
  exact Int.natCast_nonneg n

theorem mem_integers_iff_ordAt_nonneg (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔ 0 ≤ ordAt v t := by
  refine ⟨ordAt_nonneg_of_mem v t, fun h => ?_⟩
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (t : v.adicCompletion F) with ht | ht
  · exact ht
  · have ht' : ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rwa [Units.val_inv_eq_inv_val]
    have h1 := ordAt_nonneg_of_mem v t⁻¹ ht'
    rw [ordAt_inv] at h1
    have h0 : ordAt v t = 0 := le_antisymm (by omega) h
    exact ((ordAt_eq_zero_iff v t).mp h0).1

theorem unifPow_mul_val_fst (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) (u : (AdeleRing (𝓞 F) F)ˣ) :
    ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (u : AdeleRing (𝓞 F) F).1 := by
  have h1 : archUnits (unifPow ϖ k) = 1 := Units.ext (unifPow_val_fst ϖ k)
  have h : archUnits (unifPow ϖ k * u) = archUnits u := by rw [map_mul, h1, one_mul]
  exact congrArg (fun z : (InfiniteAdeleRing F)ˣ => (z : InfiniteAdeleRing F)) h

theorem unifPow_mul_val_snd_apply (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (u : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w
      = (((ϖ.ϖ w ^ k w : (w.adicCompletion F)ˣ)) : w.adicCompletion F)
          * ((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w := by
  have h : unitAtHom w (unifPow ϖ k * u) = ϖ.ϖ w ^ k w * unitAtHom w u := by
    rw [map_mul, unitAtHom_unifPow]
  have h' := congrArg Units.val h
  rw [Units.val_mul] at h'
  exact h'

theorem unifPow_mul_val_snd_apply_of_mem (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) (u : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) :
    (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w
      = ((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w := by
  rw [unifPow_mul_val_snd_apply, hk w hw, zpow_zero, Units.val_one, one_mul]

theorem unifPow_mul_mem_integralOutside_iff (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S ↔ ∀ v ∉ S, 0 ≤ k v := by
  have hu' := (mem_unitsOutside_iff S u).mp hu
  rw [mem_integralOutside_iff]
  refine forall₂_congr fun v hv => ?_
  rw [show (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((unitAtHom v (unifPow ϖ k * u) : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
    mem_integers_iff_ordAt_nonneg, map_mul, ordAt_mul, ordAt_unitAtHom_unifPow]
  have h0 : ordAt v (unitAtHom v u) = 0 := by
    rw [ordAt_eq_zero_iff]
    refine ⟨hu'.1 v hv, ?_⟩
    rw [← map_inv]
    exact hu'.2 v hv
  rw [h0, add_zero]

open scoped Classical in
theorem factorizable_apply_unifPow_mul {f : AdeleRing (𝓞 F) F → ℂ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = if ∀ v ∉ S, 0 ≤ k v then
          (∏ w, g w ((u : AdeleRing (𝓞 F) F).1 w)) * ∏ v ∈ S, h v (((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v)
        else 0 := by
  classical
  rw [hf]
  have hval : (fun x : AdeleRing (𝓞 F) F => (∏ w, g w (x.1 w)) * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v))
        ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = (∏ w, g w ((u : AdeleRing (𝓞 F) F).1 w)) * ∏ v ∈ S, h v (((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v) := by
    show (∏ w, g w (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w))
        * ∏ v ∈ S, h v ((((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v) = _
    rw [unifPow_mul_val_fst]
    congr 1
    exact Finset.prod_congr rfl fun v hv => by rw [unifPow_mul_val_snd_apply_of_mem ϖ hk u hv]
  by_cases hpos : ∀ v ∉ S, 0 ≤ k v
  · rw [if_pos hpos, Set.indicator_of_mem ((unifPow_mul_mem_integralOutside_iff ϖ hu).mpr hpos)]
    exact hval
  · rw [if_neg hpos, Set.indicator_of_notMem]
    exact fun hmem => hpos ((unifPow_mul_mem_integralOutside_iff ϖ hu).mp hmem)

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_TateSDecomp4
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_EulerBookkeeping

set_option autoImplicit false

open Finsupp Filter Topology

noncomputable section

namespace M4aLocalCFT
namespace EulerBookkeeping

variable {ι : Type*}

private def _root_.M4aLocalCFT.EulerBookkeeping.mono (a : ι → ℂ) (k : ι →₀ ℕ) : ℂ := k.prod fun i n => a i ^ n

p2m_export "M4aLocalCFT.EulerBookkeeping" "mono"
theorem mono_zero (a : ι → ℂ) : mono a 0 = 1 := Finsupp.prod_zero_index

theorem mono_add (a : ι → ℂ) (k l : ι →₀ ℕ) : mono a (k + l) = mono a k * mono a l :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem mono_single (a : ι → ℂ) (i : ι) (n : ℕ) : mono a (single i n) = a i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

theorem norm_mono (a : ι → ℂ) (k : ι →₀ ℕ) : ‖mono a k‖ = k.prod fun i n => ‖a i‖ ^ n := by
  unfold mono Finsupp.prod
  rw [norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_pow _ _

section Restricted

variable (a : ι → ℂ) [DecidableEq ι]

def sigmaT (T : Finset ι) : ℂ := ∑' k : ι →₀ ℕ, if ∀ i ∈ T, k i = 0 then mono a k else 0

variable {a}

omit [DecidableEq ι] in
theorem sigmaT_empty : sigmaT a ∅ = ∑' k, mono a k := by
  unfold sigmaT
  exact tsum_congr fun k => by simp

omit [DecidableEq ι] in
theorem summable_restrict (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (p : (ι →₀ ℕ) → Prop) [DecidablePred p] :
    Summable fun k : ι →₀ ℕ => if p k then mono a k else 0 :=
  Summable.of_norm_bounded hF fun k => by
    split_ifs
    · exact le_rfl
    · simp

omit [DecidableEq ι] in
theorem summable_norm_of_summable_mono (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    Summable fun i => ‖a i‖ := by
  have h := hF.comp_injective (Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0))
  refine h.congr fun i => ?_
  show ‖mono a (single i 1)‖ = ‖a i‖
  rw [mono_single, pow_one]

theorem sigmaT_insert (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) {T : Finset ι} {i : ι} (hi : i ∉ T) :
    sigmaT a (insert i T) = (1 - a i) * sigmaT a T := by
  set FT : (ι →₀ ℕ) → ℂ := fun k => if ∀ j ∈ T, k j = 0 then mono a k else 0 with hFT
  set G1 : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k i = 0 then mono a k else 0 with hG1
  set G2 : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k i ≠ 0 then mono a k else 0 with hG2
  have hsplit : ∀ k, FT k = G1 k + G2 k := by
    intro k
    simp only [hFT, hG1, hG2]
    by_cases h1 : ∀ j ∈ T, k j = 0
    · by_cases h2 : k i = 0
      · rw [if_pos h1, if_pos ⟨h1, h2⟩, if_neg (fun h => h.2 h2), add_zero]
      · rw [if_pos h1, if_neg (fun h => h2 h.2), if_pos ⟨h1, h2⟩, zero_add]
    · rw [if_neg h1, if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1), add_zero]
  have hins : sigmaT a (insert i T) = ∑' k, G1 k := by
    unfold sigmaT
    refine tsum_congr fun k => ?_
    simp only [hG1, Finset.forall_mem_insert, and_comm]
  have hG1s : Summable G1 := by simpa [hG1] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k i = 0)
  have hG2s : Summable G2 := by simpa [hG2] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k i ≠ 0)
  set φ : (ι →₀ ℕ) → (ι →₀ ℕ) := fun k => k + single i 1 with hφ
  have hφinj : Function.Injective φ := add_left_injective (single i 1)
  have hsupp : Function.support G2 ⊆ Set.range φ := by
    intro k hk
    have hki : k i ≠ 0 := by
      by_contra h0
      apply hk
      simp [hG2, h0]
    refine ⟨k - single i 1, ?_⟩
    show k - single i 1 + single i 1 = k
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hki))
  have hcomp : ∀ k, G2 (φ k) = FT k * a i := by
    intro k
    have hTi : (∀ j ∈ T, ((k + single i 1 : ι →₀ ℕ)) j = 0) ↔ ∀ j ∈ T, k j = 0 := by
      refine forall₂_congr fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hji, add_zero]
    have hii : ((k + single i 1 : ι →₀ ℕ)) i ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]; exact Nat.succ_ne_zero _
    simp only [hG2, hFT, hφ, hTi, hii, ne_eq, not_false_eq_true, and_true]
    split_ifs
    · rw [mono_add, mono_single, pow_one]
    · rw [zero_mul]
  have hG2sum : ∑' k, G2 k = sigmaT a T * a i := by
    rw [← hφinj.tsum_eq hsupp]
    simp only [hcomp]
    rw [tsum_mul_right]
    rfl
  have hT : sigmaT a T = ∑' k, G1 k + ∑' k, G2 k := by
    rw [← (hG1s.hasSum.add hG2s.hasSum).tsum_eq]
    unfold sigmaT
    exact tsum_congr fun k => hsplit k
  rw [hins]
  have := hT
  rw [hG2sum] at this
  linear_combination -this

theorem sigmaT_eq_prod_mul (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (T : Finset ι) :
    sigmaT a T = (∏ i ∈ T, (1 - a i)) * ∑' k, mono a k := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul, sigmaT_empty]
  | insert i T hi ih => rw [sigmaT_insert hF hi, ih, Finset.prod_insert hi, mul_assoc]

theorem norm_sigmaT_sub_one_le (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (T : Finset ι) :
    ‖sigmaT a T - 1‖ ≤ (∑' i, if i ∈ T then 0 else ‖a i‖) * ∑' k, ‖mono a k‖ := by
  set R : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k ≠ 0 then mono a k else 0 with hR
  have hRs : Summable R := by simpa [hR] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k ≠ 0)
  have hRn : Summable fun k => ‖R k‖ := by
    refine Summable.of_norm_bounded hF fun k => ?_
    simp only [hR, norm_norm]
    split_ifs
    · exact le_rfl
    · simp
  have hsub : sigmaT a T - 1 = ∑' k, R k := by
    have h0 : ∀ k : ι →₀ ℕ, (if ∀ j ∈ T, k j = 0 then mono a k else 0)
        = (if k = 0 then (1 : ℂ) else 0) + R k := by
      intro k
      by_cases hk : k = 0
      · subst hk
        simp [hR, mono_zero]
      · simp only [hR, hk, if_false, zero_add, ne_eq, not_false_eq_true, and_true]
    unfold sigmaT
    rw [tsum_congr h0, ((hasSum_ite_eq (0 : ι →₀ ℕ) (1 : ℂ)).add hRs.hasSum).tsum_eq]
    ring
  rw [hsub]
  refine (norm_tsum_le_tsum_norm hRn).trans ?_
  set A : Set (ι →₀ ℕ) := {k | (∀ j ∈ T, k j = 0) ∧ k ≠ 0} with hA
  have hRA : ∀ k, ‖R k‖ = A.indicator (fun k => ‖mono a k‖) k := by
    intro k
    simp only [hR, hA, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [tsum_congr hRA, ← tsum_subtype]
  have hne : ∀ k : A, (k.1).support.Nonempty := fun k => Finsupp.support_nonempty_iff.mpr k.2.2
  set j : A → ι := fun k => (hne k).choose with hj
  have hjmem : ∀ k : A, j k ∈ (k.1).support := fun k => (hne k).choose_spec
  have hjpos : ∀ k : A, 1 ≤ k.1 (j k) := fun k => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (hjmem k))
  have hjT : ∀ k : A, j k ∉ T := by
    intro k hkT
    exact (Finsupp.mem_support_iff.mp (hjmem k)) (k.2.1 (j k) hkT)
  set e : A → ι × (ι →₀ ℕ) := fun k => (j k, k.1 - single (j k) 1) with he
  have hdecomp : ∀ k : A, k.1 - single (j k) 1 + single (j k) 1 = k.1 := fun k =>
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (hjpos k))
  have heinj : Function.Injective e := by
    intro k k' h
    simp only [he, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    rw [← hdecomp k, ← hdecomp k', h2, h1]
  set g : ι × (ι →₀ ℕ) → ℝ := fun p => (if p.1 ∈ T then 0 else ‖a p.1‖) * ‖mono a p.2‖ with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (by split_ifs <;> simp) (norm_nonneg _)
  have hcT : Summable fun i => if i ∈ T then (0 : ℝ) else ‖a i‖ := by
    refine Summable.of_norm_bounded (summable_norm_of_summable_mono hF) fun i => ?_
    split_ifs <;> simp
  have hcTn : Summable fun i => ‖if i ∈ T then (0 : ℝ) else ‖a i‖‖ := by
    refine hcT.norm.congr fun i => ?_
    rfl
  have hFn : Summable fun k : ι →₀ ℕ => ‖‖mono a k‖‖ := by simpa using hF
  have hgs : Summable g := by
    simpa [hg] using summable_mul_of_summable_norm hcTn hFn
  have hle : ∀ k : A, ‖mono a k.1‖ ≤ g (e k) := by
    intro k
    simp only [hg, he, hjT k, if_false]
    conv_lhs => rw [← hdecomp k, mono_add, norm_mul, mono_single, pow_one, mul_comm]
  calc ∑' k : A, ‖mono a k.1‖
      ≤ ∑' p, g p := Summable.tsum_le_tsum_of_inj e heinj (fun p _ => hg0 p) hle (hF.subtype A) hgs
    _ = (∑' i, if i ∈ T then (0 : ℝ) else ‖a i‖) * ∑' k, ‖mono a k‖ := by
        rw [tsum_mul_tsum_of_summable_norm hcTn hFn]

theorem tendsto_sigmaT (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    Tendsto (fun T : Finset ι => sigmaT a T) atTop (𝓝 1) := by
  have htail : Tendsto (fun T : Finset ι => ∑' i, if i ∈ T then (0 : ℝ) else ‖a i‖) atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero fun i => ‖a i‖
    refine h.congr fun T => ?_
    refine (tsum_subtype ({x | x ∉ T} : Set ι) (fun i => ‖a i‖)).trans ?_
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ T
    · rw [if_pos hi, Set.indicator_of_notMem (by simpa using hi)]
    · rw [if_neg hi, Set.indicator_of_mem (by simpa using hi)]
  have hbound := htail.mul_const (∑' k, ‖mono a k‖)
  rw [zero_mul] at hbound
  have h0 : Tendsto (fun T : Finset ι => sigmaT a T - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => norm_sigmaT_sub_one_le hF T) hbound
  have := h0.add_const 1
  simpa using this

end Restricted
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Main

variable {a : ι → ℂ}

theorem tsum_mono_mul_tprod_one_sub (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    (∑' k, mono a k) * ∏' i, (1 - a i) = 1 := by
  classical
  have ha := summable_norm_of_summable_mono hF
  have hmult : Multipliable fun i => 1 - a i := by
    have h := multipliable_one_add_of_summable (f := fun i => -a i) (by simpa using ha)
    simpa [sub_eq_add_neg] using h
  have hprod : Tendsto (fun T : Finset ι => ∏ i ∈ T, (1 - a i)) atTop (𝓝 (∏' i, (1 - a i))) := by
    have h := hmult.hasProd
    rw [HasProd] at h
    simpa using h
  have h1 : Tendsto (fun T : Finset ι => sigmaT a T) atTop (𝓝 ((∏' i, (1 - a i)) * ∑' k, mono a k)) := by
    have h := hprod.mul_const (∑' k, mono a k)
    refine h.congr fun T => ?_
    rw [sigmaT_eq_prod_mul hF T]
  have h2 := tendsto_sigmaT hF
  have heq := tendsto_nhds_unique h1 h2
  rw [mul_comm] at heq
  exact heq

end Main
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT.EulerBookkeeping
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_EulerBookkeeping
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_EulerBookkeeping0

set_option autoImplicit false

open Finsupp Filter Topology

noncomputable section

namespace M4aLocalCFT
namespace EulerBookkeeping

variable {ι : Type*} {a : ι → ℂ}

def monoN (a : ι → ℂ) (k : ι →₀ ℕ) : ℝ := k.prod fun i n => ‖a i‖ ^ n

theorem monoN_eq_norm_mono (k : ι →₀ ℕ) : monoN a k = ‖mono a k‖ := (norm_mono a k).symm

theorem monoN_nonneg (k : ι →₀ ℕ) : 0 ≤ monoN a k := by
  rw [monoN_eq_norm_mono]; exact norm_nonneg _

theorem monoN_add (k l : ι →₀ ℕ) : monoN a (k + l) = monoN a k * monoN a l :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem monoN_single (i : ι) (n : ℕ) : monoN a (single i n) = ‖a i‖ ^ n :=
  Finsupp.prod_single_index (pow_zero _)

theorem monoN_zero : monoN a 0 = 1 := Finsupp.prod_zero_index

theorem sum_monoN_le_prod [DecidableEq ι] (h1 : ∀ i, ‖a i‖ < 1) (T : Finset ι) :
    ∀ u : Finset (ι →₀ ℕ), (∀ k ∈ u, k.support ⊆ T) → ∑ k ∈ u, monoN a k ≤ ∏ i ∈ T, (1 - ‖a i‖)⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
      intro u hu
      have hu0 : u ⊆ {0} := by
        intro k hk
        rw [Finset.mem_singleton, ← Finsupp.support_eq_empty]
        exact Finset.subset_empty.mp (hu k hk)
      calc ∑ k ∈ u, monoN a k ≤ ∑ k ∈ ({0} : Finset (ι →₀ ℕ)), monoN a k :=
            Finset.sum_le_sum_of_subset_of_nonneg hu0 fun k _ _ => monoN_nonneg k
        _ = 1 := by rw [Finset.sum_singleton, monoN_zero]
        _ = ∏ i ∈ (∅ : Finset ι), (1 - ‖a i‖)⁻¹ := (Finset.prod_empty).symm
  | insert i T hi ih =>
      intro u hu
      set φ : (ι →₀ ℕ) → ℕ × (ι →₀ ℕ) := fun k => (k i, k.erase i) with hφ
      have hφinj : Set.InjOn φ u := by
        intro k _ k' _ h
        simp only [hφ, Prod.mk.injEq] at h
        rw [← Finsupp.single_add_erase i k, ← Finsupp.single_add_erase i k', h.1, h.2]
      have hterm : ∀ k, monoN a k = ‖a i‖ ^ (φ k).1 * monoN a (φ k).2 := by
        intro k
        conv_lhs => rw [← Finsupp.single_add_erase i k, monoN_add, monoN_single]
      set N : Finset ℕ := u.image fun k => k i with hN
      set U : Finset (ι →₀ ℕ) := u.image fun k => k.erase i with hU
      have hUT : ∀ k' ∈ U, k'.support ⊆ T := by
        intro k' hk'
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hk'
        rw [Finsupp.support_erase]
        intro j hj
        have hj' := Finset.mem_erase.mp hj
        have := hu k hk hj'.2
        rcases Finset.mem_insert.mp this with h | h
        · exact (hj'.1 h).elim
        · exact h
      have himg : u.image φ ⊆ N ×ˢ U := by
        intro p hp
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hk, Finset.mem_image_of_mem _ hk⟩
      have hgeom : ∑ n ∈ N, ‖a i‖ ^ n ≤ (1 - ‖a i‖)⁻¹ := by
        rw [← tsum_geometric_of_lt_one (norm_nonneg _) (h1 i)]
        exact (summable_geometric_of_lt_one (norm_nonneg _) (h1 i)).sum_le_tsum N fun n _ => pow_nonneg (norm_nonneg _) n
      have hpos : ∀ j, 0 ≤ (1 - ‖a j‖)⁻¹ := fun j => inv_nonneg.mpr (sub_nonneg.mpr (h1 j).le)
      calc ∑ k ∈ u, monoN a k
          = ∑ k ∈ u, ‖a i‖ ^ (φ k).1 * monoN a (φ k).2 := Finset.sum_congr rfl fun k _ => hterm k
        _ = ∑ p ∈ u.image φ, ‖a i‖ ^ p.1 * monoN a p.2 :=
            (Finset.sum_image (f := fun p : ℕ × (ι →₀ ℕ) => ‖a i‖ ^ p.1 * monoN a p.2) hφinj).symm
        _ ≤ ∑ p ∈ N ×ˢ U, ‖a i‖ ^ p.1 * monoN a p.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ =>
              mul_nonneg (pow_nonneg (norm_nonneg _) _) (monoN_nonneg _)
        _ = (∑ n ∈ N, ‖a i‖ ^ n) * ∑ k' ∈ U, monoN a k' := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
        _ ≤ (1 - ‖a i‖)⁻¹ * ∏ j ∈ T, (1 - ‖a j‖)⁻¹ :=
            mul_le_mul hgeom (ih U hUT) (Finset.sum_nonneg fun k _ => monoN_nonneg k) (hpos i)
        _ = ∏ j ∈ insert i T, (1 - ‖a j‖)⁻¹ := by rw [Finset.prod_insert hi]

theorem summable_norm_div_one_sub (ha : Summable fun i => ‖a i‖) (h1 : ∀ i, ‖a i‖ < 1) :
    Summable fun i => ‖a i‖ / (1 - ‖a i‖) := by
  have hsub : ∀ i, 0 < 1 - ‖a i‖ := fun i => sub_pos.mpr (h1 i)
  have hev : ∀ᶠ i in cofinite, ‖a i‖ < 1 / 2 := ha.tendsto_cofinite_zero (eventually_lt_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually (ha.mul_left 2) ?_
  filter_upwards [hev] with i hi
  have hx : 0 ≤ ‖a i‖ / (1 - ‖a i‖) := div_nonneg (norm_nonneg _) (hsub i).le
  rw [Real.norm_eq_abs, abs_of_nonneg hx, div_le_iff₀ (hsub i)]
  nlinarith [norm_nonneg (a i)]

theorem summable_norm_mono (ha : Summable fun i => ‖a i‖) (h1 : ∀ i, ‖a i‖ < 1) :
    Summable fun k : ι →₀ ℕ => ‖mono a k‖ := by
  classical
  have hsub : ∀ i, 0 < 1 - ‖a i‖ := fun i => sub_pos.mpr (h1 i)
  set c : ι → ℝ := fun i => ‖a i‖ / (1 - ‖a i‖) with hc
  have hcs : Summable c := summable_norm_div_one_sub ha h1
  have hc0 : ∀ i, 0 ≤ c i := fun i => div_nonneg (norm_nonneg _) (hsub i).le
  have hfac : ∀ i, (1 - ‖a i‖)⁻¹ ≤ Real.exp (c i) := by
    intro i
    have heq : (1 - ‖a i‖)⁻¹ = c i + 1 := by
      simp only [hc]
      field_simp [(hsub i).ne']
      ring
    rw [heq]
    exact Real.add_one_le_exp (c i)
  refine (summable_of_sum_le (f := fun k : ι →₀ ℕ => monoN a k) (c := Real.exp (∑' i, c i))
    (fun k => monoN_nonneg k) fun u => ?_).congr fun k => monoN_eq_norm_mono k
  set T : Finset ι := u.biUnion fun k => k.support with hT
  have hu : ∀ k ∈ u, k.support ⊆ T := fun k hk => Finset.subset_biUnion_of_mem (fun k => k.support) hk
  calc ∑ k ∈ u, monoN a k ≤ ∏ i ∈ T, (1 - ‖a i‖)⁻¹ := sum_monoN_le_prod h1 T u hu
    _ ≤ ∏ i ∈ T, Real.exp (c i) :=
        Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (hsub i).le) fun i _ => hfac i
    _ = Real.exp (∑ i ∈ T, c i) := (Real.exp_sum T c).symm
    _ ≤ Real.exp (∑' i, c i) := Real.exp_le_exp.mpr (hcs.sum_le_tsum T fun i _ => hc0 i)

end M4aLocalCFT.EulerBookkeeping
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_EulerBookkeeping0
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_PlaceSum

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain"

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk InfinitePlace.Completion RingOfIntegers RingOfIntegers.coe_injective InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside ideleNorm_mul localChar_apply"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type*} [Field F] [NumberField F]

abbrev underZ (v : HeightOneSpectrum (𝓞 F)) : Ideal ℤ := v.asIdeal.under ℤ

theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem underZ_ne_bot (v : HeightOneSpectrum (𝓞 F)) : underZ v ≠ ⊥ := by
  intro h
  have hmem : ((Ideal.absNorm v.asIdeal : ℤ)) ∈ underZ v := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem v.asIdeal
  rw [h, Ideal.mem_bot] at hmem
  exact absNorm_ne_zero v (by exact_mod_cast hmem)

theorem absNorm_underZ_dvd (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (underZ v) ∣ Ideal.absNorm v.asIdeal := by
  have hinj : Function.Injective (Ideal.quotientMap v.asIdeal (algebraMap ℤ (𝓞 F)) le_rfl) :=
    Ideal.quotientMap_injective
  have h := AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap v.asIdeal (algebraMap ℤ (𝓞 F)) le_rfl).toAddMonoidHom hinj
  rwa [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]

theorem absNorm_underZ_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm (underZ v) := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact underZ_ne_bot v

theorem absNorm_underZ_le (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm (underZ v) ≤ Ideal.absNorm v.asIdeal :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_ne_zero v)) (absNorm_underZ_dvd v)

theorem card_filter_underZ_le [DecidableEq (Ideal ℤ)] (U : Finset (HeightOneSpectrum (𝓞 F))) (q : Ideal ℤ)
    (hq : ∃ v ∈ U, underZ v = q) :
    (U.filter fun v => underZ v = q).card ≤ Module.finrank ℚ F := by
  obtain ⟨v₀, _, hv₀⟩ := hq
  haveI : v₀.asIdeal.IsMaximal := v₀.isPrime.isMaximal v₀.ne_bot
  haveI : q.IsMaximal := hv₀ ▸ (Ideal.IsMaximal.under ℤ v₀.asIdeal)
  have hq0 : q ≠ ⊥ := hv₀ ▸ underZ_ne_bot v₀
  refine le_trans ?_ (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hq0)
  refine Finset.card_le_card_of_injOn (fun v => v.asIdeal) (fun v hv => ?_) ?_
  · rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hq0]
    exact ⟨v.isPrime, ⟨hv.2.symm⟩⟩
  · intro v _ w _ h
    exact HeightOneSpectrum.ext h

theorem int_ideal_eq_span_absNorm (q : Ideal ℤ) : q = Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)} := by
  set g : ℤ := Submodule.IsPrincipal.generator q with hg
  have hq : q = Ideal.span {g} := (Submodule.IsPrincipal.span_singleton_generator q).symm
  rw [hq, Ideal.absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply, Int.span_natAbs]

theorem summable_absNorm_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  classical
  set g : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hgs : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hdecay : ∀ v : HeightOneSpectrum (𝓞 F),
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ g (Ideal.absNorm (underZ v)) := by
    intro v
    refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by linarith)
    · exact_mod_cast absNorm_underZ_pos v
    · exact_mod_cast absNorm_underZ_le v
  refine summable_of_sum_le (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c := Module.finrank ℚ F * ∑' n, g n)
    fun U => ?_
  set key : HeightOneSpectrum (𝓞 F) → Ideal ℤ := underZ with hkey
  calc ∑ v ∈ U, (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)
      ≤ ∑ v ∈ U, g (Ideal.absNorm (key v)) := Finset.sum_le_sum fun v _ => hdecay v
    _ = ∑ q ∈ U.image key, ((U.filter fun v => key v = q).card : ℝ) * g (Ideal.absNorm q) := by
        rw [Finset.sum_comp (fun q : Ideal ℤ => g (Ideal.absNorm q)) key]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [nsmul_eq_mul]
    _ ≤ ∑ q ∈ U.image key, (Module.finrank ℚ F : ℝ) * g (Ideal.absNorm q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_underZ_le U q ⟨v, hv, hvq⟩) (hg0 _)
    _ = (Module.finrank ℚ F : ℝ) * ∑ q ∈ U.image key, g (Ideal.absNorm q) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑ n ∈ (U.image key).image Ideal.absNorm, g n := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hinj : Set.InjOn (fun q : Ideal ℤ => Ideal.absNorm q) ↑(U.image key) := by
          intro q _ q' _ h
          rw [int_ideal_eq_span_absNorm q, int_ideal_eq_span_absNorm q']
          simp only at h
          rw [h]
        exact le_of_eq (Finset.sum_image hinj).symm
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑' n, g n :=
        mul_le_mul_of_nonneg_left (hgs.sum_le_tsum _ fun n _ => hg0 n) (Nat.cast_nonneg _)

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_PlaceSum
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_ShellBound

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField IsDedekindDomain P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.EulerBookkeeping"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT

namespace ShellBound

variable {F : Type} [Field F] [NumberField F]

theorem distribHaarChar_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (unifPow ϖ k)
      = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-n) := by
  rw [unifPow, Finsupp.prod, Finsupp.prod, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow, TateGlobal.distribHaarChar_embUnit_eq_local,
    LocalHaarModulus.distribHaarChar_adicCompletion]
  have h1 : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ.ϖ v)) = 1 :=
    ϖ.ordAt_eq_one v
  rw [h1, ← zpow_mul, neg_one_mul]

theorem ideleNorm_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ideleNorm F (unifPow ϖ k) = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ)) ^ (-n) := by
  rw [ideleNorm, distribHaarChar_unifPow, Finsupp.prod, Finsupp.prod, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [NNReal.coe_zpow, NNReal.coe_natCast]

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := TateGlobal.absNorm_ne_zero v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    intro h
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

def baseFam (F : Type) [Field F] [NumberField F] (σ : ℝ) :
    HeightOneSpectrum (𝓞 F) → ℂ :=
  fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) : ℝ) : ℂ)

theorem norm_baseFam (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖baseFam F σ v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  rw [baseFam, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

theorem summable_norm_baseFam {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ‖baseFam F σ v‖ := by
  refine (TateGlobal.summable_absNorm_rpow_neg hσ).congr fun v => ?_
  rw [norm_baseFam]

theorem norm_baseFam_lt_one {σ : ℝ} (hσ : 1 < σ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖baseFam F σ v‖ < 1 := by
  rw [norm_baseFam]
  refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith)
  exact_mod_cast one_lt_absNorm v

theorem norm_mono_baseFam (σ : ℝ) (m : HeightOneSpectrum (𝓞 F) →₀ ℕ) :
    ‖mono (baseFam F σ) m‖ = m.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n := by
  rw [mono, Finsupp.prod, Finsupp.prod, norm_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [norm_pow, norm_baseFam]

def toNatVec (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : HeightOneSpectrum (𝓞 F) →₀ ℕ :=
  k.mapRange Int.toNat rfl

theorem mono_baseFam_toNatVec (σ : ℝ) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ‖mono (baseFam F σ) (toNatVec k)‖
      = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat := by
  rw [norm_mono_baseFam, toNatVec, Finsupp.prod_mapRange_index (fun v => pow_zero _)]

omit [NumberField F] in
theorem toNatVec_injOn {k₁ k₂ : HeightOneSpectrum (𝓞 F) →₀ ℤ}
    (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂) (h : toNatVec k₁ = toNatVec k₂) : k₁ = k₂ := by
  ext v
  have hv := congrArg (fun m => m v) h
  simp only [toNatVec, Finsupp.mapRange_apply] at hv
  have hv₁ : 0 ≤ k₁ v := Finsupp.le_def.mp h₁ v
  have hv₂ : 0 ≤ k₂ v := Finsupp.le_def.mp h₂ v
  omega

theorem summable_of_shell_bound {S : Finset (HeightOneSpectrum (𝓞 F))} {σ : ℝ} (hσ : 1 < σ)
    (c : ExpIndex (F := F) S → ℝ) (hc0 : ∀ k, 0 ≤ c k) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k : ExpIndex (F := F) S, 0 ≤ k.1 →
      c k ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat) * M)
    (hz : ∀ k : ExpIndex (F := F) S, ¬ 0 ≤ k.1 → c k = 0) :
    Summable c := by
  classical
  have hEB : Summable fun m : HeightOneSpectrum (𝓞 F) →₀ ℕ => ‖mono (baseFam F σ) m‖ :=
    summable_norm_mono (summable_norm_baseFam hσ) (norm_baseFam_lt_one hσ)
  refine summable_of_sum_le hc0 (c := M * ∑' m, ‖mono (baseFam F σ) m‖) fun u => ?_
  have hsub : ∑ k ∈ u, c k = ∑ k ∈ u.filter (fun k => 0 ≤ k.1), c k := by
    refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
    by_contra hneg
    exact hk (hz k hneg)
  rw [hsub]
  have hstep : ∑ k ∈ u.filter (fun k => 0 ≤ k.1), c k
      ≤ ∑ k ∈ u.filter (fun k => 0 ≤ k.1), ‖mono (baseFam F σ) (toNatVec k.1)‖ * M := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hcone : 0 ≤ k.1 := (Finset.mem_filter.mp hk).2
    calc c k ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat) * M :=
          hb k hcone
      _ = ‖mono (baseFam F σ) (toNatVec k.1)‖ * M := by rw [mono_baseFam_toNatVec]
  refine hstep.trans ?_
  rw [← Finset.sum_mul, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left ?_ hM
  have hinj : Set.InjOn (fun k : ExpIndex (F := F) S => toNatVec k.1)
      ↑(u.filter (fun k => 0 ≤ k.1)) := fun k₁ h₁ k₂ h₂ he =>
    Subtype.ext (toNatVec_injOn (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2 he)
  have himg : ∑ k ∈ u.filter (fun k => 0 ≤ k.1), ‖mono (baseFam F σ) (toNatVec k.1)‖
      = ∑ m ∈ (u.filter (fun k => 0 ≤ k.1)).image (fun k => toNatVec k.1),
          ‖mono (baseFam F σ) m‖ :=
    (Finset.sum_image (f := fun m => ‖mono (baseFam F σ) m‖) hinj).symm
  rw [himg]
  exact hEB.sum_le_tsum _ fun m _ => norm_nonneg _

end ShellBound
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_ShellBound
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_ShellTranslate

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume"

open AutomorphicForm IsDedekindDomain M4aLocalCFT

p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

open scoped NNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ShellTranslate

variable {F : Type} [Field F] [NumberField F]

theorem setIntegral_smul_eq' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    {U : Set (AdeleRing (𝓞 F) F)ˣ} (hU : MeasurableSet U) (g : (AdeleRing (𝓞 F) F)ˣ)
    (G : (AdeleRing (𝓞 F) F)ˣ → E) :
    ∫ x in g • U, G x ∂ν = ∫ u in U, G (g * u) ∂ν := by
  have hgU : MeasurableSet (g • U) := hU.const_smul g
  rw [← integral_indicator hgU, ← integral_indicator hU, ← integral_mul_left_eq_self _ g]
  congr 1
  funext u
  have hiff : g * u ∈ g • U ↔ u ∈ U := by
    constructor
    · intro h
      obtain ⟨u', hu', h'⟩ := Set.mem_smul_set.mp h
      rw [smul_eq_mul] at h'
      rw [← mul_left_cancel h']
      exact hu'
    · intro hu
      exact Set.mem_smul_set.mpr ⟨u, hu, rfl⟩
  simp only [Set.indicator]
  by_cases hu : u ∈ U
  · rw [if_pos (hiff.mpr hu), if_pos hu]
  · rw [if_neg (mt hiff.mp hu), if_neg hu]

theorem norm_zetaIntegrand {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχu : IsUnitaryChar (𝓞 F) F χ) (f : AdeleRing (𝓞 F) F → ℂ) (s : ℂ)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    ‖f ↑x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖
      = ‖f ↑x‖ * ideleNorm F x ^ s.re := by
  rw [norm_mul, norm_mul, hχu x, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos x)]

theorem ideleNorm_unifPow_rpow (ϖ : Uniformizers F) (σ : ℝ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    ideleNorm F (unifPow ϖ k) ^ σ
      = k.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ n.toNat := by
  rw [ShellBound.ideleNorm_unifPow, Finsupp.prod, Finsupp.prod,
    ← Real.finsetProd_rpow _ _ (fun v _ => zpow_nonneg (Nat.cast_nonneg _) _) σ]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hn : 0 ≤ k v := Finsupp.le_def.mp hk v
  have ha : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (ShellBound.one_lt_absNorm v).le
  calc ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(k v))) ^ σ
      = ((Ideal.absNorm v.asIdeal : ℝ) ^ ((-(k v) : ℤ) : ℝ)) ^ σ := by
        rw [Real.rpow_intCast]
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (((-(k v) : ℤ) : ℝ) * σ) := by
        rw [← Real.rpow_mul ha.le]
    _ = (Ideal.absNorm v.asIdeal : ℝ) ^ ((-σ) * ((k v).toNat : ℝ)) := by
        congr 1
        have hcast : (((k v).toNat : ℕ) : ℝ) = ((k v : ℤ) : ℝ) := by
          exact_mod_cast congrArg (Int.cast (R := ℝ)) (Int.toNat_of_nonneg hn)
        rw [hcast]
        push_cast
        ring
    _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ ((k v).toNat : ℝ) := by
        rw [Real.rpow_mul ha.le]
    _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ (k v).toNat := by
        rw [Real.rpow_natCast]

theorem setIntegral_shell_norm_le [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] (ϖ : Uniformizers F)
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    {f : AdeleRing (𝓞 F) F → ℂ} {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχu : IsUnitaryChar (𝓞 F) F χ) {s : ℂ} {M : ℝ}
    (k : ExpIndex (F := F) S) (hk : 0 ≤ k.1)
    (hM : ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
        ‖f ↑(unifPow ϖ k.1 * u)‖ * ideleNorm F u ^ s.re ∂ν ≤ M) :
    ∫ x in shell S k.1, ‖f ↑x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν
      ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat) * M := by
  have hC0 : 0 ≤ k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat := by
    rw [Finsupp.prod]
    exact Finset.prod_nonneg fun v _ =>
      pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
  have hpt : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      ‖f ↑(unifPow ϖ k.1 * u) * ((χ (unifPow ϖ k.1 * u) : ℂˣ) : ℂ)
          * ((ideleNorm F (unifPow ϖ k.1 * u) : ℝ) : ℂ) ^ s‖
        = (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat)
          * (‖f ↑(unifPow ϖ k.1 * u)‖ * ideleNorm F u ^ s.re) := fun u => by
    rw [norm_zetaIntegrand hχu, ideleNorm_mul,
      Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le,
      ideleNorm_unifPow_rpow ϖ s.re hk]
    ring
  rw [shell_eq_smul ϖ k.2, setIntegral_smul_eq' ν (isOpen_unitsOutside S).measurableSet]
  simp only [hpt]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hM hC0

end ShellTranslate
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_ShellTranslate
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Fold_G2Proof

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume"

open AutomorphicForm IsDedekindDomain M4aLocalCFT

p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal"

open scoped NNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace G2Proof

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.TateGlobal.countable_heightOneSpectrum

def unifOf (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) : Uniformizers F where
  ϖ := ϖ
  ordAt_eq_one v := by
    have h : WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ v))))
        = WithZero.exp (-1 : ℤ) := by
      rw [← ValuedOrdBridge.valued_coe_units_eq_exp_neg_ord]
      exact hϖ v
    have h' := WithZero.exp_injective h
    show ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ v)) = 1
    omega

theorem unifOf_ϖ (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    (unifOf ϖ hϖ).ϖ = ϖ := rfl

theorem unifPow_zero (ϖ : Uniformizers F) : unifPow ϖ (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) = 1 :=
  Finsupp.prod_zero_index

theorem ofReal_pow_cpow {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (s : ℂ) :
    (((x ^ m : ℝ)) : ℂ) ^ s = (((x : ℝ) : ℂ) ^ s) ^ m := by
  have h : (x ^ m : ℝ) = ∏ _i ∈ Finset.range m, x := by
    rw [Finset.prod_const, Finset.card_range]
  rw [h, cpow_prod_ofReal_nonneg _ _ (fun _ _ => hx), Finset.prod_const, Finset.card_range]

theorem ofReal_inv_natCast_pow_cpow (N : ℕ) (m : ℕ) (s : ℂ) :
    ((((N : ℝ)⁻¹ ^ m : ℝ)) : ℂ) ^ s = (((N : ℕ) : ℂ) ^ (-s)) ^ m := by
  rw [ofReal_pow_cpow (inv_nonneg.mpr (Nat.cast_nonneg N)) m s]
  congr 1
  have harg : ((N : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

theorem ideleNorm_unifPow_cpow (ϖ : Uniformizers F) (s : ℂ) {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    ((ideleNorm F (unifPow ϖ k) : ℝ) : ℂ) ^ s
      = k.prod fun v n => ((((Ideal.absNorm v.asIdeal : ℕ)) : ℂ) ^ (-s)) ^ n.toNat := by
  rw [ShellBound.ideleNorm_unifPow, Finsupp.prod, Finsupp.prod,
    cpow_prod_ofReal_nonneg _ _ (fun v _ => zpow_nonneg (Nat.cast_nonneg _) _) s]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k v = m := Int.eq_ofNat_of_zero_le (Finsupp.le_def.mp hk v)
  rw [hm, Int.toNat_natCast, zpow_neg, ← inv_zpow, zpow_natCast]
  exact ofReal_inv_natCast_pow_cpow _ m s

theorem coe_char_unifPow (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    ((χ (unifPow ϖ k) : ℂˣ) : ℂ) = k.prod fun v n => ((localChar χ v (ϖ.ϖ v) : ℂˣ) : ℂ) ^ n.toNat := by
  rw [char_unifPow, Finsupp.prod, Finsupp.prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k v = m := Int.eq_ofNat_of_zero_le (Finsupp.le_def.mp hk v)
  rw [hm, Int.toNat_natCast, zpow_natCast, Units.val_pow_eq_pow_val]

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def placeFactor (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ((localChar χ v (ϖ.ϖ v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ)) : ℂ) ^ (-s)

def shellCoef (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : ℂ := by
  classical exact if 0 ≤ k then k.prod (fun v n => placeFactor χ ϖ s v ^ n.toNat) else 0

theorem shellCoef_of_nonneg (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    shellCoef χ ϖ s k = k.prod (fun v n => placeFactor χ ϖ s v ^ n.toNat) := by
  simp only [shellCoef, if_pos hk]

theorem shellCoef_of_not_nonneg (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ¬ 0 ≤ k) : shellCoef χ ϖ s k = 0 := by
  simp only [shellCoef, if_neg hk]

omit [NumberField F] in
theorem not_forall_nonneg_of_not_nonneg {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0)
    (hk : ¬ 0 ≤ k) : ¬ ∀ v ∉ S, 0 ≤ k v := fun h' =>
  hk (Finsupp.le_def.mpr fun v => by
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hv : v ∈ S
    · exact (hkS v hv).symm.le
    · exact h' v hv)

section TestFunction

variable {S}

variable {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

theorem apply_unifPow_mul_eq (hf : IsFactorizableStandardOutside f S g h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = f (u : AdeleRing (𝓞 F) F) := by
  have e1 := factorizable_apply_unifPow_mul hf ϖ hkS hu
  have e0 := factorizable_apply_unifPow_mul hf ϖ (k := 0) (fun _ _ => rfl) hu
  rw [if_pos (show ∀ v ∉ S, 0 ≤ k v from fun v _ => Finsupp.le_def.mp hk v)] at e1
  rw [if_pos (show ∀ v ∉ S, 0 ≤ (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) v from fun _ _ => le_rfl),
    unifPow_zero ϖ, one_mul] at e0
  exact e1.trans e0.symm

theorem apply_unifPow_mul_eq_zero (hf : IsFactorizableStandardOutside f S g h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : ¬ 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 0 := by
  rw [factorizable_apply_unifPow_mul hf ϖ hkS hu, if_neg (not_forall_nonneg_of_not_nonneg S hkS hk)]

theorem zetaIntegrand_unifPow_mul (hf : IsFactorizableStandardOutside f S g h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * ((χ (unifPow ϖ k * u) : ℂˣ) : ℂ)
        * ((ideleNorm F (unifPow ϖ k * u) : ℝ) : ℂ) ^ s
      = (k.prod fun v n => placeFactor χ ϖ s v ^ n.toNat)
          * (f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s) := by
  rw [apply_unifPow_mul_eq hf ϖ hkS hk hu, map_mul, Units.val_mul, ideleNorm_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos _).le (ideleNorm_pos _).le,
    coe_char_unifPow χ ϖ hk, ideleNorm_unifPow_cpow ϖ s hk]
  have hprod : (k.prod fun v n => placeFactor χ ϖ s v ^ n.toNat)
      = (k.prod fun v n => ((localChar χ v (ϖ.ϖ v) : ℂˣ) : ℂ) ^ n.toNat)
          * k.prod fun v n => ((((Ideal.absNorm v.asIdeal : ℕ)) : ℂ) ^ (-s)) ^ n.toNat := by
    rw [← Finsupp.prod_mul]
    simp only [placeFactor, mul_pow]
  rw [hprod]
  ring

end TestFunction
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section PerShell

variable {S}

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

variable {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem preimage_mul_smul (c : (AdeleRing (𝓞 F) F)ˣ) (U : Set (AdeleRing (𝓞 F) F)ˣ) :
    (fun u => c * u) ⁻¹' (c • U) = U := by
  ext u
  constructor
  · rintro ⟨u', hu', he⟩
    rwa [← mul_left_cancel (show c * u' = c * u from he)]
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem setIntegral_unitsOutside_translate (hf : IsFactorizableStandardOutside f S g h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (k : ExpIndex (F := F) S) :
    ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
        f ((unifPow ϖ k.1 * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
          * ((χ (unifPow ϖ k.1 * u) : ℂˣ) : ℂ) * ((ideleNorm F (unifPow ϖ k.1 * u) : ℝ) : ℂ) ^ s ∂ν
      = shellCoef χ ϖ s k.1
          * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
              f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s ∂ν := by
  by_cases hk : 0 ≤ k.1
  · rw [shellCoef_of_nonneg χ ϖ s hk, ← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_unitsOutside S).measurableSet fun u hu => ?_
    exact zetaIntegrand_unifPow_mul hf χ ϖ s k.2 hk hu
  · rw [shellCoef_of_not_nonneg χ ϖ s hk, zero_mul]
    refine (setIntegral_congr_fun (isOpen_unitsOutside S).measurableSet fun u hu => ?_).trans
      (integral_zero _ _)
    rw [apply_unifPow_mul_eq_zero hf ϖ k.2 hk hu, zero_mul, zero_mul]

theorem integrableOn_shell (hf : IsFactorizableStandardOutside f S g h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    [ν.IsMulLeftInvariant] (k : ExpIndex (F := F) S)
    (hU : IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν) :
    IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (shell S k.1) ν := by
  by_cases hk : 0 ≤ k.1
  · rw [shell_eq_smul ϖ k.2]
    have hemb : MeasurableEmbedding (fun u : (AdeleRing (𝓞 F) F)ˣ => unifPow ϖ k.1 * u) :=
      (Homeomorph.mulLeft (unifPow ϖ k.1)).measurableEmbedding
    have hmp := measurePreserving_mul_left ν (unifPow ϖ k.1)
    rw [← hmp.integrableOn_comp_preimage hemb, preimage_mul_smul]
    have h1 : IntegrableOn (fun u : (AdeleRing (𝓞 F) F)ˣ =>
        (k.1.prod fun v n => placeFactor χ ϖ s v ^ n.toNat)
          * (f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s))
        (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν := hU.const_mul _
    exact (integrableOn_congr_fun (fun u hu => zetaIntegrand_unifPow_mul hf χ ϖ s k.2 hk hu)
      (isOpen_unitsOutside S).measurableSet).mpr h1
  · refine (integrableOn_congr_fun (fun x hx => ?_) (measurableSet_shell ϖ k.2)).mpr integrableOn_zero
    rw [shell_eq_smul ϖ k.2] at hx
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
    rw [smul_eq_mul, apply_unifPow_mul_eq_zero hf ϖ k.2 hk hu, zero_mul, zero_mul]

theorem setIntegral_shell_norm_le' (hf : IsFactorizableStandardOutside f S g h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) (ϖ : Uniformizers F) (s : ℂ)
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] (k : ExpIndex (F := F) S) (hk : 0 ≤ k.1) :
    ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν
      ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat)
          * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), ‖f (u : AdeleRing (𝓞 F) F)‖
              * ideleNorm F u ^ s.re ∂ν :=
  ShellTranslate.setIntegral_shell_norm_le ν ϖ hχu k hk (le_of_eq
    (setIntegral_congr_fun (isOpen_unitsOutside S).measurableSet fun u hu => by
      rw [apply_unifPow_mul_eq hf ϖ k.2 hk hu]))

theorem setIntegral_shell_norm_eq_zero (hf : IsFactorizableStandardOutside f S g h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) (k : ExpIndex (F := F) S) (hk : ¬ 0 ≤ k.1) :
    ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν = 0 := by
  refine (setIntegral_congr_fun (measurableSet_shell ϖ k.2) fun x hx => ?_).trans (integral_zero _ _)
  rw [shell_eq_smul ϖ k.2] at hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [smul_eq_mul, apply_unifPow_mul_eq_zero hf ϖ k.2 hk hu, zero_mul, zero_mul, norm_zero]

theorem integrable_of_integrableOn_unitsOutside (hf : IsFactorizableStandardOutside f S g h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) (ϖ : Uniformizers F)
    {s : ℂ} (hs : 1 < s.re) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    (hU : IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := by
  have hint : ∀ k : ExpIndex (F := F) S, IntegrableOn
      (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (shell S k.1) ν := fun k => integrableOn_shell hf χ ϖ s ν k hU
  have hsum : Summable fun k : ExpIndex (F := F) S =>
      ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν :=
    ShellBound.summable_of_shell_bound hs _ (fun k => integral_nonneg fun x => norm_nonneg _)
      (integral_nonneg fun u => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ideleNorm_pos u).le _))
      (fun k hk => setIntegral_shell_norm_le' hf hχu ϖ s ν k hk)
      (fun k hk => setIntegral_shell_norm_eq_zero hf χ ϖ s ν k hk)
  have hall := MeasureTheory.integrableOn_iUnion_of_summable_integral_norm hint hsum
  rw [iUnion_shell] at hall
  exact integrableOn_univ.mp hall

theorem integral_eq_tsum_shellCoef_mul (hf : IsFactorizableStandardOutside f S g h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) (ϖ : Uniformizers F)
    {s : ℂ} (hs : 1 < s.re) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] :
    ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν
      = (∑' k : ExpIndex (F := F) S, shellCoef χ ϖ s k.1)
          * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
              f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s ∂ν := by
  by_cases hU : IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ =>
      f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν
  · have hsum := hasSum_setIntegral_unitsOutside ν ϖ S
      (integrable_of_integrableOn_unitsOutside hf hχu ϖ hs ν hU)
    have hsum' : HasSum (fun k : ExpIndex (F := F) S => shellCoef χ ϖ s k.1
        * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
            f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s ∂ν)
        (∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν) :=
      hsum.congr_fun fun k => (setIntegral_unitsOutside_translate hf χ ϖ s ν k).symm
    rw [← hsum'.tsum_eq, tsum_mul_right]
  · have hI : ¬ Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := fun hI => hU hI.integrableOn
    rw [integral_undef hI, integral_undef hU, mul_zero]

end PerShell
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Reindex

def liftVec (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.embDomain (Function.Embedding.subtype _) (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero m)

omit [NumberField F] in
theorem liftVec_apply_of_not_mem (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : liftVec S m v = ((m ⟨v, hv⟩ : ℕ) : ℤ) := by
  have e := Finsupp.embDomain_apply_self (Function.Embedding.subtype fun v => v ∉ S)
    (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero m) ⟨v, hv⟩
  rw [Finsupp.mapRange_apply] at e
  exact e

omit [NumberField F] in
theorem liftVec_apply_of_mem (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : liftVec S m v = 0 := by
  refine Finsupp.embDomain_notin_range _ _ _ fun ⟨i, hi⟩ => ?_
  have h : (i : HeightOneSpectrum (𝓞 F)) = v := hi
  exact i.2 (h ▸ hv)

omit [NumberField F] in
theorem liftVec_nonneg (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) : 0 ≤ liftVec S m :=
  Finsupp.le_def.mpr fun v => by
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hv : v ∈ S
    · rw [liftVec_apply_of_mem S m hv]
    · rw [liftVec_apply_of_not_mem S m hv]
      exact Int.natCast_nonneg _

def liftIdx (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) : ExpIndex (F := F) S :=
  ⟨liftVec S m, fun _ hv => liftVec_apply_of_mem S m hv⟩

omit [NumberField F] in
theorem liftIdx_injective : Function.Injective (liftIdx (F := F) S) := fun _ _ he =>
  Finsupp.mapRange_injective (fun n : ℕ => (n : ℤ)) Nat.cast_zero Nat.cast_injective
    (Finsupp.embDomain_injective _ (congrArg Subtype.val he))

omit [NumberField F] in
theorem mem_range_liftIdx {k : ExpIndex (F := F) S} (hk : 0 ≤ k.1) : k ∈ Set.range (liftIdx (F := F) S) := by
  refine ⟨Finsupp.subtypeDomain (fun v => v ∉ S) (Finsupp.mapRange Int.toNat Int.toNat_zero k.1),
    Subtype.ext (Finsupp.ext fun v => ?_)⟩
  show liftVec S _ v = k.1 v
  by_cases hv : v ∈ S
  · rw [liftVec_apply_of_mem S _ hv, k.2 v hv]
  · rw [liftVec_apply_of_not_mem S _ hv, Finsupp.subtypeDomain_apply, Finsupp.mapRange_apply]
    exact Int.toNat_of_nonneg (Finsupp.le_def.mp hk v)

theorem shellCoef_liftIdx (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) :
    shellCoef χ ϖ s (liftIdx S m).1
      = EulerBookkeeping.mono (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => placeFactor χ ϖ s v.1) m := by
  show shellCoef χ ϖ s (liftVec S m) = _
  rw [shellCoef_of_nonneg χ ϖ s (liftVec_nonneg S m)]
  show (liftVec S m).prod (fun v n => placeFactor χ ϖ s v ^ n.toNat) = m.prod fun v n => placeFactor χ ϖ s v.1 ^ n
  rw [liftVec, Finsupp.prod_embDomain, Finsupp.prod_mapRange_index (fun _ => by rw [Int.toNat_zero, pow_zero])]
  refine Finsupp.prod_congr fun v _ => ?_
  rw [Int.toNat_natCast]
  rfl

theorem tsum_shellCoef_eq_tsum_mono (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) :
    ∑' k : ExpIndex (F := F) S, shellCoef χ ϖ s k.1
      = ∑' m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ,
          EulerBookkeeping.mono (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => placeFactor χ ϖ s v.1) m := by
  have hsupp : Function.support (fun k : ExpIndex (F := F) S => shellCoef χ ϖ s k.1)
      ⊆ Set.range (liftIdx (F := F) S) := by
    intro k hk
    by_cases hk0 : 0 ≤ k.1
    · exact mem_range_liftIdx S hk0
    · exact absurd (shellCoef_of_not_nonneg χ ϖ s hk0) hk
  rw [← (liftIdx_injective S).tsum_eq hsupp]
  exact tsum_congr fun m => shellCoef_liftIdx S χ ϖ s m

theorem norm_placeFactor {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : Uniformizers F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖placeFactor χ ϖ s v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  rw [placeFactor, norm_mul, localChar_apply, hχu, one_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (absNorm_ne_zero v)), Complex.neg_re]

theorem summable_norm_mono_placeFactor {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : Uniformizers F) {s : ℂ} (hs : 1 < s.re) :
    Summable fun m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ =>
      ‖EulerBookkeeping.mono (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => placeFactor χ ϖ s v.1) m‖ := by
  have hnorm : ∀ v : HeightOneSpectrum (𝓞 F), ‖placeFactor χ ϖ s v‖ = ‖ShellBound.baseFam F s.re v‖ := fun v => by
    rw [norm_placeFactor hχu, ShellBound.norm_baseFam]
  refine EulerBookkeeping.summable_norm_mono ?_ fun v => ?_
  · have h := (ShellBound.summable_norm_baseFam (F := F) hs).comp_injective
      (Subtype.val_injective (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ S))
    exact h.congr fun v => (hnorm v.1).symm
  · rw [hnorm]
    exact ShellBound.norm_baseFam_lt_one hs v.1

end Reindex
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

theorem hole_G2 (F : Type) [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    [BorelSpace (AdeleRing (𝓞 F) F)ˣ] (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        (Summable fun k : {v // v ∉ S} →₀ ℕ =>
            ‖EulerBookkeeping.mono (fun v : {v // v ∉ S} => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) k‖) ∧
        zetaIntegral ν f χ s
          = (c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s)
            * ∑' k : {v // v ∉ S} →₀ ℕ,
                EulerBookkeeping.mono (fun v : {v // v ∉ S} => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) k := by
  letI : ∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ := fun _ => ⟨rfl⟩
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ := fun _ => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ := fun _ => ⟨rfl⟩
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ := fun _ => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ := fun _ => ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
  refine ⟨(refConst S μa μf ν : ℝ), refConst_pos S μa μf ν, ?_⟩
  intro f g h hf χ hχc hχu hχS s hs
  have hsum := summable_norm_mono_placeFactor S hχu (unifOf ϖ hϖ) hs
  refine ⟨hsum, ?_⟩
  have hshell := integral_eq_tsum_shellCoef_mul (S := S) hf hχu (unifOf ϖ hϖ) hs ν
  have hmaster := setIntegral_unitsOutside_zetaIntegrand_eq S μa μf ν hf χ hχc hχS s
  have hre := tsum_shellCoef_eq_tsum_mono S χ (unifOf ϖ hϖ) s
  show ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν = _
  rw [hshell, hmaster, hre]
  unfold placeFactor
  simp only [unifOf_ϖ]
  ring

theorem zetaIntegral_mul_eulerFactors_eq_impl (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s := by
  obtain ⟨c, hc, H⟩ := hole_G2 F ν S μf μa ϖ hϖ
  refine ⟨c, hc, fun f g h _hf χ _hχc _hχu _hχS s _hs => ?_⟩
  obtain ⟨hS, hZ⟩ := H f g h _hf χ _hχc _hχu _hχS s _hs
  rw [hZ, mul_assoc, EulerBookkeeping.tsum_mono_mul_tprod_one_sub hS, mul_one]

end G2Proof
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

end Fold_G2Proof
p2m_reactivate "P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.M4aLocalCFT"

open MeasureTheory _root_.NumberField _root_.P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField AutomorphicForm IsDedekindDomain _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.NumberField.TateGlobal in

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s :=
  M4aLocalCFT.G2Proof.zetaIntegral_mul_eulerFactors_eq_impl F ν S μf μa ϖ hϖ

#print axioms solution

end S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq
end P2MW
export P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq (solution)
