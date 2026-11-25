-- Prove2me | solution 1 for GlobalTheory.HL.EichCont.prod_eich_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:26.955143+00:00
-- url     : https://prove2.me/submissions/089a1af0-3654-4537-9235-13f739605544

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductContinuousOnLattice
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_add_mul
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
namespace GlobalTheory.HL.EichCont
section Abstract
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ}
variable {O}
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden
end Abstract
section Eich
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
end Eich
section Lat
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {O : Subring E} {N : ℕ}
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden
end Lat
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private lemma exists_algebraMap_mul_mem_O {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (z : E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧ algebraMap F E a * z ∈ L.O := by
  have hint : ∀ t : F, ∃ s : F, s ≠ 0 ∧ s ∈ (valuation F).integer ∧
      s * t ∈ (valuation F).integer := by
    intro t
    by_cases ht : valuation F t ≤ 1
    · exact ⟨1, one_ne_zero, (valuation F).integer.one_mem, by
        rw [one_mul, Valuation.mem_integer_iff]; exact ht⟩
    · have ht0 : t ≠ 0 := by rintro rfl; exact ht (by simp)
      refine ⟨t⁻¹, inv_ne_zero ht0, ?_, by
        rw [inv_mul_cancel₀ ht0]; exact (valuation F).integer.one_mem⟩
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 ht))
  obtain ⟨ω, hωO, e, -, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  obtain ⟨x, y, hxy⟩ := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := F) (L.cj : E →+* E)
    (fun x => L.cj_cj x) (fun r => L.cj.commutes r)
    (fun x hx => by obtain ⟨a, ha⟩ := (L.cj_fix x).1 hx; exact ⟨a, ha⟩)
    ⟨⟨_, e, hωe, by rw [mul_comm]; exact hωe⟩, rfl⟩ z
  obtain ⟨s₁, hs₁0, hs₁, hs₁x⟩ := hint x
  obtain ⟨s₂, hs₂0, hs₂, hs₂y⟩ := hint y
  have hO : ∀ t ∈ (valuation F).integer, algebraMap F E t ∈ L.O :=
    fun t ht => (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L t).2 ht
  refine ⟨s₁ * s₂, mul_ne_zero hs₁0 hs₂0, hO _ ((valuation F).integer.mul_mem hs₁ hs₂), ?_⟩
  rw [hxy]
  have : algebraMap F E (s₁ * s₂) * (algebraMap F E x + algebraMap F E y * ω) =
      algebraMap F E s₂ * algebraMap F E (s₁ * x) +
        algebraMap F E s₁ * algebraMap F E (s₂ * y) * ω := by
    simp only [map_mul]; ring
  rw [this]
  exact L.O.add_mem (L.O.mul_mem (hO _ hs₂) (hO _ hs₁x))
    (L.O.mul_mem (L.O.mul_mem (hO _ hs₁) (hO _ hs₂y)) hωO)
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_algebraMap_mul_mem_O_forall {κ : Type} [Fintype κ] (z : κ → E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ ∀ k, algebraMap F E a * z k ∈ O := by
  choose a ha0 haO haz using fun k => hden (z k)
  refine ⟨∏ k, a k, Finset.prod_ne_zero_iff.2 fun k _ => ha0 k, ?_, fun k => ?_⟩
  · rw [map_prod]
    exact O.prod_mem fun k _ => haO k
  · rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k' _ => haO k') (haz k)
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_algebraMap_mem_O_Bd_inv (A : Module.End E (Fin N → E)) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ _root_.GlobalTheory.HL.EichCont.Bd O A a⁻¹ := by
  obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : Fin N × Fin N => A (fun k => if p.1 = k then 1 else 0) p.2)
  refine ⟨a, ha0, haO, fun m hm => ⟨algebraMap F E a • A m, fun i => ?_, ?_⟩⟩
  · rw [LinearMap.pi_apply_eq_sum_univ A m]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact O.sum_mem fun j _ => by
      rw [mul_left_comm]
      exact O.mul_mem (hm j) (haz (j, i))
  · rw [smul_smul, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_zero' (t : F) : _root_.GlobalTheory.HL.EichCont.Bd O (0 : Module.End E (Fin N → E)) t :=
  fun _ _ => ⟨0, fun _ => O.zero_mem, by simp⟩
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma IntV_smul_of_mem {o : E} (ho : o ∈ O) {m : Fin N → E}
    (hm : _root_.GlobalTheory.HL.EichCont.IntV O m) : _root_.GlobalTheory.HL.EichCont.IntV O (o • m) :=
  fun j => by simpa using O.mul_mem ho (hm j)
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_of_Bd_mul_of_mem_O {A : Module.End E (Fin N → E)} {s o : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A (s * o)) (ho : algebraMap F E o ∈ O) :
    _root_.GlobalTheory.HL.EichCont.Bd O A s := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  exact ⟨algebraMap F E o • m₁, IntV_smul_of_mem ho hm₁, by rw [e₁, map_mul, mul_smul]⟩
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_of_eq {A : Module.End E (Fin N → E)} {s t : F} (h : s = t)
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) : _root_.GlobalTheory.HL.EichCont.Bd O A t := h ▸ hA
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma IntV_add' {m m' : Fin N → E} (hm : _root_.GlobalTheory.HL.EichCont.IntV O m)
    (hm' : _root_.GlobalTheory.HL.EichCont.IntV O m') : _root_.GlobalTheory.HL.EichCont.IntV O (m + m') :=
  fun j => O.add_mem (hm j) (hm' j)
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_add' {A B : Module.End E (Fin N → E)} {t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A t) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A + B) t := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hB m hm
  exact ⟨m₁ + m₂, IntV_add' hm₁ hm₂, by rw [LinearMap.add_apply, e₁, e₂, smul_add]⟩
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
private lemma Bd_mul' {A B : Module.End E (Fin N → E)} {s t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A * B) (s * t) := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hB m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hA m₁ hm₁
  refine ⟨m₂, hm₂, ?_⟩
  rw [Module.End.mul_apply, e₁, map_smul, e₂, smul_smul, ← map_mul, mul_comm t s]
open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ} in
variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_Bd_prod_sub_of_Bd_sub : ∀ (r : ℕ) (A : Fin r → Module.End E (Fin N → E)) (c : F),
    c ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ G : Fin r → Module.End E (Fin N → E),
      (∀ i, _root_.GlobalTheory.HL.EichCont.Bd O (G i - A i) d) →
        _root_.GlobalTheory.HL.EichCont.Bd O ((List.ofFn G).prod - (List.ofFn A).prod) c := by
  intro r
  induction r with
  | zero =>
    intro A c _
    exact ⟨1, one_ne_zero, fun G _ => by
      simp only [List.ofFn_zero, List.prod_nil, sub_self]
      exact Bd_zero' c⟩
  | succ r ih =>
    intro A c hc
    obtain ⟨a, ha0, haO, hA0⟩ := exists_algebraMap_mem_O_Bd_inv hden (A 0)
    obtain ⟨b, hb0, hbO, hAs⟩ := exists_algebraMap_mem_O_Bd_inv hden (List.ofFn fun i => A i.succ).prod
    obtain ⟨w, hw0, hwO, hwc⟩ := hden (algebraMap F E c)
    obtain ⟨d₁, hd₁0, hd₁⟩ := ih (fun i => A i.succ) (c * a * b * w) (by simp [hc, ha0, hb0, hw0])
    obtain ⟨z, hz0, hzO, hz⟩ := exists_algebraMap_mul_mem_O_forall hden
      ![algebraMap F E (c * b), algebraMap F E d₁]
    have hz1 : algebraMap F E z * algebraMap F E (c * b) ∈ O := hz 0
    have hz2 : algebraMap F E z * algebraMap F E d₁ ∈ O := hz 1
    refine ⟨c * b * d₁ * z, by simp [hc, hb0, hd₁0, hz0], fun G hG => ?_⟩
    have hG0 : _root_.GlobalTheory.HL.EichCont.Bd O (G 0 - A 0) (c * b) :=
      Bd_of_Bd_mul_of_mem_O (o := d₁ * z) (Bd_of_eq (by ring) (hG 0))
        (by rw [map_mul, mul_comm]; exact hz2)
    have hGs : ∀ i : Fin r, _root_.GlobalTheory.HL.EichCont.Bd O (G i.succ - A i.succ) d₁ := fun i =>
      Bd_of_Bd_mul_of_mem_O (o := c * b * z) (Bd_of_eq (by ring) (hG i.succ))
        (by rw [map_mul, mul_comm]; exact hz1)
    have hrest := hd₁ (fun i => G i.succ) hGs
    have hGsb : _root_.GlobalTheory.HL.EichCont.Bd O (List.ofFn fun i => G i.succ).prod b⁻¹ := by
      have h1 : _root_.GlobalTheory.HL.EichCont.Bd O
          ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) b⁻¹ :=
        Bd_of_Bd_mul_of_mem_O (o := c * a * b * w * b) (Bd_of_eq (by field_simp) hrest) (by
          have := O.mul_mem (O.mul_mem (O.mul_mem hwc haO) hbO) hbO
          simp only [map_mul]
          convert this using 1
          ring)
      have := Bd_add' hAs h1
      rwa [add_sub_cancel] at this
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have key : G 0 * (List.ofFn fun i => G i.succ).prod - A 0 * (List.ofFn fun i => A i.succ).prod =
        (G 0 - A 0) * (List.ofFn fun i => G i.succ).prod +
          A 0 * ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) := by
      rw [sub_mul, mul_sub]
      abel
    rw [key]
    refine Bd_add' ?_ ?_
    · exact Bd_of_eq (by field_simp) (Bd_mul' hG0 hGsb)
    · exact Bd_of_Bd_mul_of_mem_O (o := b * w) (Bd_of_eq (by field_simp) (Bd_mul' hA0 hrest))
        (by rw [map_mul]; exact O.mul_mem hbO hwO)
end GlobalTheory.HL.EichCont
end
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichCont
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.EichCont
namespace _root_.GlobalTheory.HL.EichCont
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E)
    (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (he : ∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v)
    (Λ : Submodule L.O (Fin N → E)) (hΛ : _root_.GlobalTheory.HL.IsLat L Λ) (c : Fˣ),
    ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E)
      (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)),
      (∀ i v, e' i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u' i) (s' i) v) →
      (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) →
      (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) →
      ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x =
        algebraMap F E c • y := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm X u s e he Λ hΛ c
  have hden := exists_algebraMap_mul_mem_O L
  obtain ⟨β, hβ0, hβO, hβ⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : (Fin N × Fin N) ⊕ (Fin r × Fin N) =>
      Sum.elim (fun q => Hm q.1 q.2) (fun q => X q.1 q.2) p)
  have hH : ∀ i j, algebraMap F E β * Hm i j ∈ L.O := fun i j => hβ (Sum.inl (i, j))
  have hX : ∀ i k, algebraMap F E β * X i k ∈ L.O := fun i k => hβ (Sum.inr (i, k))
  have hXc : ∀ i k, algebraMap F E β * L.cj (X i k) ∈ L.O := fun i k => by
    have := _root_.GlobalTheory.UnramOrder.cj_mem L (hX i k)
    rwa [map_mul, L.cj.commutes] at this

  have hform1 : ∀ v o : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → _root_.GlobalTheory.HL.EichCont.IntV L.O o →
      algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v o ∈ L.O := by
    intro v o hv ho
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (_root_.GlobalTheory.UnramOrder.cj_mem L (ho b))
    convert this using 1
    ring
  have hform2 : ∀ v : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → ∀ i,
      algebraMap F E β * algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v (X i) ∈ L.O := by
    intro v hv i
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (hXc i b)
    convert this using 1
    ring
  have hsub : ∀ v w w' : Fin N → E, _root_.GlobalTheory.HL.hf L Hm v w -
      _root_.GlobalTheory.HL.hf L Hm v w' = _root_.GlobalTheory.HL.hf L Hm v (w - w') := by
    intro v w w'
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmul : ∀ (v o : Fin N → E) (t : F), _root_.GlobalTheory.HL.hf L Hm v
      (algebraMap F E t • o) = algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
    intro v o t
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdiff : ∀ i (u₁ : Fin N → E) (s₁ : E) (t : F) (o : Fin N → E) (o' : E) (v : Fin N → E),
      u₁ - u i = algebraMap F E t • o → s₁ - s i = algebraMap F E t * o' →
      _root_.GlobalTheory.HL.eich L Hm (X i) u₁ s₁ v - _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v =
        algebraMap F E t • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
          _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i)) := by
    intro i u₁ s₁ t o o' v hu hs
    have hu' : u₁ = u i + algebraMap F E t • o := by rw [← hu]; abel
    have hs' : s₁ = s i + algebraMap F E t * o' := by rw [← hs]; ring
    have h1 : _root_.GlobalTheory.HL.hf L Hm v u₁ = _root_.GlobalTheory.HL.hf L Hm v (u i) +
        algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
      rw [← hsmul, ← hu, ← hsub]; ring
    unfold _root_.GlobalTheory.HL.eich
    rw [h1, hu', hs']
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hbr : ∀ i (o : Fin N → E) (o' : E) (v : Fin N → E), _root_.GlobalTheory.HL.EichCont.IntV L.O v →
      _root_.GlobalTheory.HL.EichCont.IntV L.O o → o' ∈ L.O →
      _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E (β ^ 3) • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
        _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i))) := by
    intro i o o' v hv ho ho' k
    have t1 := L.O.mul_mem (L.O.mul_mem (hform1 v o hv ho) (hX i k)) hβO
    have t2 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) hβO) (ho k)
    have t3 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) ho') (hX i k)
    have := L.O.sub_mem t1 (L.O.add_mem t2 t3)
    convert this using 1
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_pow]
    ring
  let φ : ((Fin N → E) ≃ₗ[E] (Fin N → E)) →* Module.End E (Fin N → E) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hP : ∀ (f : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (y : Fin N → E),
      (List.ofFn f).prod y = (List.ofFn fun i => φ (f i)).prod y := by
    intro f y
    have : φ (List.ofFn f).prod = (List.ofFn fun i => φ (f i)).prod := by
      rw [map_list_prod, List.map_ofFn]; rfl
    rw [← this]; rfl
  obtain ⟨a, ha0, haO, ha⟩ : ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧
      ∀ x ∈ Λ, _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E a • x) := by
    obtain ⟨S, hS⟩ := hΛ.1
    obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
      (fun p : S × Fin N => (p.1 : Fin N → E) p.2)
    refine ⟨a, ha0, haO, fun x hx => ?_⟩
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact fun j => haz (⟨y, hy⟩, j)
    | zero => exact fun j => by simp
    | add y z _ _ hy hz => exact fun j => by simpa [mul_add] using L.O.add_mem (hy j) (hz j)
    | smul o y _ hy =>
      exact fun j => by simpa [Subring.smul_def, mul_left_comm] using L.O.mul_mem o.2 (hy j)
  obtain ⟨b, hb0, hbO, hb⟩ : ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧
      ∀ m, _root_.GlobalTheory.HL.EichCont.IntV L.O m → algebraMap F E b • m ∈ Λ := by
    have hstep : ∀ w ∈ Submodule.span E (Λ : Set (Fin N → E)),
        ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧ algebraMap F E b • w ∈ Λ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simpa using hy⟩
      | zero => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨b₂, h₂0, h₂O, h₂⟩ := hz
        refine ⟨b₁ * b₂, mul_ne_zero h₁0 h₂0, by rw [map_mul]; exact L.O.mul_mem h₁O h₂O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E b₂, h₂O⟩ : L.O) h₁
        have e2 := Λ.smul_mem (⟨algebraMap F E b₁, h₁O⟩ : L.O) h₂
        have := Λ.add_mem e1 e2
        convert this using 1
        simp only [Subring.smul_def, smul_smul, map_mul, smul_add, mul_comm]
      | smul t y _ hy =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨w₁, hw0, hwO, hwt⟩ := hden t
        refine ⟨w₁ * b₁, mul_ne_zero hw0 h₁0, by rw [map_mul]; exact L.O.mul_mem hwO h₁O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E w₁ * t, hwt⟩ : L.O) h₁
        convert e1 using 1
        rw [Subring.smul_def, smul_smul, smul_smul, map_mul]
        congr 1
        show _ = algebraMap F E w₁ * t * algebraMap F E b₁
        ring
    choose bj hbj0 hbjO hbj using fun j : Fin N =>
      hstep (fun k => if j = k then (1 : E) else 0) (by rw [hΛ.2]; exact Submodule.mem_top)
    refine ⟨∏ j, bj j, Finset.prod_ne_zero_iff.2 fun j _ => hbj0 j,
      by rw [map_prod]; exact L.O.prod_mem fun j _ => hbjO j, fun m hm => ?_⟩
    have hej : ∀ j, algebraMap F E (∏ k, bj k) • (fun k => if j = k then (1 : E) else 0) ∈ Λ := by
      intro j
      have hO' : algebraMap F E (∏ k ∈ Finset.univ.erase j, bj k) ∈ L.O := by
        rw [map_prod]; exact L.O.prod_mem fun k _ => hbjO k
      have := Λ.smul_mem (⟨_, hO'⟩ : L.O) (hbj j)
      rwa [Subring.smul_def, smul_smul, ← map_mul,
        Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at this
    rw [pi_eq_sum_univ m, Finset.smul_sum]
    refine Λ.sum_mem fun j _ => ?_
    rw [smul_comm]
    exact Λ.smul_mem (⟨m j, hm j⟩ : L.O) (hej j)
  obtain ⟨γ, hγ0, -, hγ⟩ := exists_algebraMap_mem_O_Bd_inv hden
    ((List.ofFn e).prod.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)).toLinearMap
  obtain ⟨d₀, hd₀0, hd₀⟩ := exists_Bd_prod_sub_of_Bd_sub hden r (fun i => φ (e i))
    ((c : F) * b * a * γ) (by simp [hb0, ha0, hγ0])
  refine ⟨Units.mk0 (d₀ * β ^ 3) (by simp [hd₀0, hβ0]), fun u' s' e' he' hu' hs' x hx => ?_⟩
  choose ou hou hueq using hu'
  choose os hos hseq using hs'
  have hfac : ∀ i, _root_.GlobalTheory.HL.EichCont.Bd L.O (φ (e' i) - φ (e i)) d₀ := by
    intro i m hm
    refine ⟨_, hbr i (ou i) (os i) m hm (fun j => hou i j) (hos i), ?_⟩
    have := hdiff i (u' i) (s' i) (d₀ * β ^ 3) (ou i) (os i) m
      (funext fun j => by rw [Pi.sub_apply, hueq i j, Units.val_mk0]; rfl)
      (by rw [hseq i, Units.val_mk0])
    show e' i m - e i m = _
    rw [he', he, this, smul_smul, ← map_mul]
  obtain ⟨m₁, hm₁, e₁⟩ := hd₀ (fun i => φ (e' i)) hfac _ (ha x hx)
  obtain ⟨m₂, hm₂, e₂⟩ := hγ m₁ hm₁
  have e₂' : ((List.ofFn e).prod).symm m₁ = algebraMap F E γ⁻¹ • m₂ := e₂
  refine ⟨algebraMap F E b • m₂, hb m₂ hm₂, ?_⟩
  have hx' : (List.ofFn e').prod x - (List.ofFn e).prod x = algebraMap F E a⁻¹ •
      (algebraMap F E ((c : F) * b * a * γ) • m₁) := by
    rw [← e₁, LinearMap.sub_apply, ← hP e', ← hP e, map_smul, map_smul, ← smul_sub, smul_smul,
      ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]
  calc ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x
      = ((List.ofFn e).prod).symm ((List.ofFn e').prod x - (List.ofFn e).prod x) := by
        rw [map_sub, LinearEquiv.symm_apply_apply]
    _ = algebraMap F E (c : F) • algebraMap F E b • m₂ := by
        rw [hx', smul_smul, ← map_mul, map_smul, e₂', smul_smul, ← map_mul, smul_smul, ← map_mul]
        congr 2
        field_simp
end _root_.GlobalTheory.HL.EichCont
end GlobalTheory.HL.EichCont
