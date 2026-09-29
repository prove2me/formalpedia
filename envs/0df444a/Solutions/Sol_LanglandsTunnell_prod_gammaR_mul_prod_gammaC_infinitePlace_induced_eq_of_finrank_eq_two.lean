-- Prove2me | solution 1 for LanglandsTunnell.prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2efa1b64-7905-5b3a-8e93-063e75379290

import Mathlib
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two

set_option autoImplicit false

open NumberField Complex LanglandsTunnell NumberField.InfinitePlace

namespace ArchGammaSol

variable {E : Type} [Field E] [NumberField E] {M : Type} [Field M] [NumberField M] [Algebra E M]

omit [NumberField E] [NumberField M] in
theorem liesOver_of_comap_eq {w : InfinitePlace E} {w' : InfinitePlace M}
    (h : w'.comap (algebraMap E M) = w) : w'.1.LiesOver w.1 :=
  ⟨congrArg Subtype.val h⟩

omit [NumberField E] [NumberField M] in
theorem mem_placesOver_iff {w : InfinitePlace E} {w' : InfinitePlace M} :
    w' ∈ placesOver M w ↔ w'.comap (algebraMap E M) = w :=
  ⟨fun h => @LiesOver.comap_eq _ _ _ _ _ w' w h, fun h => liesOver_of_comap_eq h⟩

theorem fibre_cases (h2 : Module.finrank E M = 2) (w : InfinitePlace E) :
    (∃ w₁ w₂ : InfinitePlace M, w₁ ≠ w₂ ∧ w₁.comap (algebraMap E M) = w ∧ w₂.comap (algebraMap E M) = w ∧
      w₁.IsUnramified E ∧ w₂.IsUnramified E ∧
      ∀ w' : InfinitePlace M, w'.comap (algebraMap E M) = w → w' = w₁ ∨ w' = w₂) ∨
    (∃ w₁ : InfinitePlace M, w₁.comap (algebraMap E M) = w ∧ w₁.IsRamified E ∧
      ∀ w' : InfinitePlace M, w'.comap (algebraMap E M) = w → w' = w₁) := by
  have hcount := unramifedPlacesOver_ncard_add_eq_finrank M w
  rw [h2] at hcount
  have hunion := union_ramifiedPlacesOver_unramifiedPlacesOver M w
  have hRfin : (ramifiedPlacesOver M w).Finite := Set.toFinite _
  have hUfin : (unramifiedPlacesOver M w).Finite := Set.toFinite _
  have hall : ∀ w' : InfinitePlace M, w'.comap (algebraMap E M) = w → w' ∈ placesOver M w :=
    fun w' h => mem_placesOver_iff.mpr h
  rcases Nat.eq_zero_or_pos (ramifiedPlacesOver M w).ncard with hR0 | hRpos
  ·
    have hU2 : (unramifiedPlacesOver M w).ncard = 2 := by omega
    obtain ⟨w₁, w₂, hne, hU⟩ := Set.ncard_eq_two.mp hU2
    have hRempty : ramifiedPlacesOver M w = ∅ := (Set.ncard_eq_zero hRfin).mp hR0
    left
    have hw₁ : w₁ ∈ unramifiedPlacesOver M w := by rw [hU]; exact Set.mem_insert _ _
    have hw₂ : w₂ ∈ unramifiedPlacesOver M w := by rw [hU]; exact Set.mem_insert_of_mem _ rfl
    refine ⟨w₁, w₂, hne, mem_placesOver_iff.mp hw₁.1, mem_placesOver_iff.mp hw₂.1, hw₁.2, hw₂.2,
      fun w' hw' => ?_⟩
    have hmem := hall w' hw'
    rw [← hunion, hRempty, Set.empty_union, hU] at hmem
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr h
  ·
    have hR1 : (ramifiedPlacesOver M w).ncard = 1 := by omega
    have hU0 : (unramifiedPlacesOver M w).ncard = 0 := by omega
    obtain ⟨w₁, hRset⟩ := Set.ncard_eq_one.mp hR1
    have hUempty : unramifiedPlacesOver M w = ∅ := (Set.ncard_eq_zero hUfin).mp hU0
    right
    have hw₁ : w₁ ∈ ramifiedPlacesOver M w := by rw [hRset]; exact Set.mem_singleton _
    refine ⟨w₁, mem_placesOver_iff.mp hw₁.1, hw₁.2, fun w' hw' => ?_⟩
    have hmem := hall w' hw'
    rw [← hunion, hUempty, Set.union_empty, hRset] at hmem
    exact hmem

theorem depfun_congr {K : Type} [Field K] {p : InfinitePlace K → Prop} {β : Type} (F : ∀ v : InfinitePlace K, p v → β)
    {v v' : InfinitePlace K} (h : v = v') (hv : p v) (hv' : p v') : F v hv = F v' hv' := by
  subst h; rfl

end ArchGammaSol

open ArchGammaSol _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.NumberField.InfinitePlace in
open scoped Classical in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (U : ∀ w : InfinitePlace E, w.IsReal → ℂ) (a : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (V : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (k : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (U' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ) (a' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (V' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ) (k' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ)
    (d : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (hd : ∀ (w₁ w₂ : InfinitePlace M) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal), w₁ ≠ w₂ →
      w₁.comap (algebraMap E M) = w₂.comap (algebraMap E M) → d w₁ h₁ + d w₂ h₂ = 1)
    (hU' : ∀ w', ∀ hw' : w'.IsReal,
      U' w' hw' = U (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    (ha' : ∀ w', ∀ hw' : w'.IsReal,
      a' w' hw' = a (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)) + d w' hw')
    (hV' : ∀ w', ∀ hw' : w'.IsComplex,
      V' w' hw' = if h : (w'.comap (algebraMap E M)).IsReal then U _ h
        else V _ (InfinitePlace.not_isReal_iff_isComplex.mp h))
    (hk' : ∀ w', ∀ hw' : w'.IsComplex,
      (k' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (k _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs)
    (s : ℂ) :
    (∏ w' : {w' : InfinitePlace M // w'.IsReal},
        Gammaℝ (s + (U' w'.1 w'.2 + signShift (a' w'.1 w'.2)))) *
      ∏ w' : {w' : InfinitePlace M // w'.IsComplex},
        Gammaℂ (s + (V' w'.1 w'.2 + ((k' w'.1 w'.2).natAbs : ℂ) / 2)) =
    (∏ w : {w : InfinitePlace E // w.IsReal},
        Gammaℝ (s + (U w.1 w.2 + signShift (a w.1 w.2))) *
          Gammaℝ (s + (U w.1 w.2 + signShift (1 + a w.1 w.2)))) *
      ∏ w : {w : InfinitePlace E // w.IsComplex},
        Gammaℂ (s + (V w.1 w.2 + ((k w.1 w.2).natAbs : ℂ) / 2)) ^ 2 := by
  classical

  set A : {w' : InfinitePlace M // w'.IsReal} → ℂ :=
    fun w' => Gammaℝ (s + (U' w'.1 w'.2 + signShift (a' w'.1 w'.2))) with hA
  set B : {w' : InfinitePlace M // w'.IsComplex} → ℂ :=
    fun w' => Gammaℂ (s + (V' w'.1 w'.2 + ((k' w'.1 w'.2).natAbs : ℂ) / 2)) with hB
  set R : {w : InfinitePlace E // w.IsReal} → ℂ :=
    fun w => Gammaℝ (s + (U w.1 w.2 + signShift (a w.1 w.2))) *
      Gammaℝ (s + (U w.1 w.2 + signShift (1 + a w.1 w.2))) with hR
  set Cc : {w : InfinitePlace E // w.IsComplex} → ℂ :=
    fun w => Gammaℂ (s + (V w.1 w.2 + ((k w.1 w.2).natAbs : ℂ) / 2)) ^ 2 with hCc
  show (∏ w', A w') * (∏ w', B w') = (∏ w, R w) * ∏ w, Cc w

  let Φ : InfinitePlace E → ℂ := fun w =>
    if h : w.IsReal then R ⟨w, h⟩ else Cc ⟨w, not_isReal_iff_isComplex.mp h⟩
  have hRHS : (∏ w, R w) * (∏ w, Cc w) = ∏ w, Φ w := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun w : InfinitePlace E => w.IsReal)]
    congr 1
    · rw [Finset.prod_subtype (Finset.univ.filter fun w : InfinitePlace E => w.IsReal)
        (p := fun w : InfinitePlace E => w.IsReal) (by simp)]
      exact Finset.prod_congr rfl fun w _ => by simp only [Φ, dif_pos w.2]
    · rw [Finset.prod_subtype (Finset.univ.filter fun w : InfinitePlace E => ¬ w.IsReal)
        (p := fun w : InfinitePlace E => w.IsComplex) (by simp [not_isReal_iff_isComplex])]
      exact Finset.prod_congr rfl fun w _ => by
        simp only [Φ, dif_neg (not_isReal_iff_isComplex.mpr w.2)]

  have hLHS : (∏ w', A w') * (∏ w', B w') = ∏ w : InfinitePlace E,
      ((∏ x ∈ Finset.univ.filter (fun x : {w' : InfinitePlace M // w'.IsReal} =>
          x.1.comap (algebraMap E M) = w), A x) *
       (∏ y ∈ Finset.univ.filter (fun y : {w' : InfinitePlace M // w'.IsComplex} =>
          y.1.comap (algebraMap E M) = w), B y)) := by
    rw [Finset.prod_mul_distrib,
      Finset.prod_fiberwise Finset.univ (fun x : {w' : InfinitePlace M // w'.IsReal} =>
        x.1.comap (algebraMap E M)) A,
      Finset.prod_fiberwise Finset.univ (fun y : {w' : InfinitePlace M // w'.IsComplex} =>
        y.1.comap (algebraMap E M)) B]
  rw [hLHS, hRHS]
  refine Finset.prod_congr rfl fun w _ => ?_

  have hv : ∀ e : ZMod 2, e = 0 ∨ e = 1 := fun e => by
    fin_cases e
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases fibre_cases h2 w with ⟨w₁, w₂, hne, hc₁, hc₂, hu₁, hu₂, hall⟩ | ⟨w₁, hc₁, hr₁, hall⟩
  ·
    by_cases hw : w.IsReal
    ·
      have hr : ∀ w' : InfinitePlace M, w'.comap (algebraMap E M) = w → w'.IsUnramified E → w'.IsReal := by
        intro w' hc hu
        rcases isUnramified_iff.mp hu with h | h
        · exact h
        · rw [hc] at h
          exact absurd hw (not_isReal_iff_isComplex.mpr h)
      have h₁ := hr w₁ hc₁ hu₁
      have h₂ := hr w₂ hc₂ hu₂
      have hRM : Finset.univ.filter (fun x : {w' : InfinitePlace M // w'.IsReal} =>
          x.1.comap (algebraMap E M) = w) = {⟨w₁, h₁⟩, ⟨w₂, h₂⟩} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          rcases hall x.1 hx with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · rintro (rfl | rfl)
          · exact hc₁
          · exact hc₂
      have hCM : Finset.univ.filter (fun y : {w' : InfinitePlace M // w'.IsComplex} =>
          y.1.comap (algebraMap E M) = w) = ∅ := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hy
        rcases hall y.1 hy with h | h
        · exact not_isReal_iff_isComplex.mpr y.2 (h ▸ h₁)
        · exact not_isReal_iff_isComplex.mpr y.2 (h ▸ h₂)
      have hne' : (⟨w₁, h₁⟩ : {w' : InfinitePlace M // w'.IsReal}) ≠ ⟨w₂, h₂⟩ :=
        fun h => hne (congrArg Subtype.val h)
      rw [hRM, hCM, Finset.prod_empty, mul_one, Finset.prod_pair hne']
      simp only [Φ, dif_pos hw, hA, hR]
      have eU₁ : U' w₁ h₁ = U w hw := by rw [hU']; exact depfun_congr U hc₁ _ _
      have eU₂ : U' w₂ h₂ = U w hw := by rw [hU']; exact depfun_congr U hc₂ _ _
      have ea₁ : a' w₁ h₁ = a w hw + d w₁ h₁ := by rw [ha']; congr 1; exact depfun_congr a hc₁ _ _
      have ea₂ : a' w₂ h₂ = a w hw + d w₂ h₂ := by rw [ha']; congr 1; exact depfun_congr a hc₂ _ _
      have hsum := hd w₁ w₂ h₁ h₂ hne (hc₁.trans hc₂.symm)
      rw [eU₁, eU₂, ea₁, ea₂]
      rcases hv (d w₁ h₁) with hd₁ | hd₁
      · have hd₂ : d w₂ h₂ = 1 := by rw [hd₁, zero_add] at hsum; exact hsum
        rw [hd₁, hd₂, add_zero, add_comm (a w hw) 1]
      · have hd₂ : d w₂ h₂ = 0 := by
          rw [hd₁] at hsum
          have := congrArg (· - 1) hsum
          simpa using this
        rw [hd₁, hd₂, add_zero, add_comm (a w hw) 1, mul_comm]
    ·
      have hwc : w.IsComplex := not_isReal_iff_isComplex.mp hw
      have hcx : ∀ w' : InfinitePlace M, w'.comap (algebraMap E M) = w → w'.IsComplex := by
        intro w' hc
        by_contra h
        have h' : w'.IsReal := not_isComplex_iff_isReal.mp h
        exact hw (hc ▸ h'.comap (algebraMap E M))
      have h₁ := hcx w₁ hc₁
      have h₂ := hcx w₂ hc₂
      have hCM : Finset.univ.filter (fun y : {w' : InfinitePlace M // w'.IsComplex} =>
          y.1.comap (algebraMap E M) = w) = {⟨w₁, h₁⟩, ⟨w₂, h₂⟩} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hy
          rcases hall y.1 hy with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · rintro (rfl | rfl)
          · exact hc₁
          · exact hc₂
      have hRM : Finset.univ.filter (fun x : {w' : InfinitePlace M // w'.IsReal} =>
          x.1.comap (algebraMap E M) = w) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hx
        rcases hall x.1 hx with h | h
        · exact not_isReal_iff_isComplex.mpr (h ▸ h₁ : x.1.IsComplex) x.2
        · exact not_isReal_iff_isComplex.mpr (h ▸ h₂ : x.1.IsComplex) x.2
      have hne' : (⟨w₁, h₁⟩ : {w' : InfinitePlace M // w'.IsComplex}) ≠ ⟨w₂, h₂⟩ :=
        fun h => hne (congrArg Subtype.val h)
      rw [hRM, hCM, Finset.prod_empty, one_mul, Finset.prod_pair hne']
      simp only [Φ, dif_neg hw, hB, hCc]
      have hnr₁ : ¬ (w₁.comap (algebraMap E M)).IsReal := by rw [hc₁]; exact hw
      have hnr₂ : ¬ (w₂.comap (algebraMap E M)).IsReal := by rw [hc₂]; exact hw
      have eV₁ : V' w₁ h₁ = V w hwc := by
        rw [hV', dif_neg hnr₁]; exact depfun_congr V hc₁ _ _
      have eV₂ : V' w₂ h₂ = V w hwc := by
        rw [hV', dif_neg hnr₂]; exact depfun_congr V hc₂ _ _
      have ek₁ : (k' w₁ h₁).natAbs = (k w hwc).natAbs := by
        rw [hk', dif_neg hnr₁]; congr 1; exact depfun_congr k hc₁ _ _
      have ek₂ : (k' w₂ h₂).natAbs = (k w hwc).natAbs := by
        rw [hk', dif_neg hnr₂]; congr 1; exact depfun_congr k hc₂ _ _
      rw [eV₁, eV₂, ek₁, ek₂, sq]
  ·
    have h₁ : w₁.IsComplex := hr₁.isComplex
    have hw : w.IsReal := hc₁ ▸ hr₁.isReal
    have hRM : Finset.univ.filter (fun x : {w' : InfinitePlace M // w'.IsReal} =>
        x.1.comap (algebraMap E M) = w) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hx
      have := hall x.1 hx
      exact not_isReal_iff_isComplex.mpr (this ▸ h₁ : x.1.IsComplex) x.2
    have hCM : Finset.univ.filter (fun y : {w' : InfinitePlace M // w'.IsComplex} =>
        y.1.comap (algebraMap E M) = w) = {⟨w₁, h₁⟩} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hy
        exact Subtype.ext (hall y.1 hy)
      · rintro rfl
        exact hc₁
    rw [hRM, hCM, Finset.prod_empty, one_mul, Finset.prod_singleton]
    simp only [Φ, dif_pos hw, hB, hR]
    have hcr : (w₁.comap (algebraMap E M)).IsReal := by rw [hc₁]; exact hw
    have eV : V' w₁ h₁ = U w hw := by
      rw [hV', dif_pos hcr]; exact depfun_congr U hc₁ _ _
    have ek : (k' w₁ h₁).natAbs = 0 := by rw [hk', dif_pos hcr]
    rw [eV, ek, Nat.cast_zero, zero_div, add_zero, ← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    rcases hv (a w hw) with ha | ha
    · rw [ha]
      simp only [signShift_zero, add_zero, show (1 : ZMod 2) + 0 = 1 by decide, signShift_one, add_assoc]
    · rw [ha, signShift_one, show (1 : ZMod 2) + 1 = 0 by decide, signShift_zero, add_zero, add_assoc,
        mul_comm]

end S_LanglandsTunnell_prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two (solution)
