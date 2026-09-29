-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c7d88080-d43b-5ac7-998f-d3490d72c8e5

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_torusChar3_mul_halfModulus3_of_linearIndependent_domRestrict_of_le_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 halfModulus3 torusChar3 principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor gl3AmbientRightTranslate upperUnipotent3 LocalGL3 le_one_of_linearIndependent_domRestrict_of_upperUnipotent3 eq_torusChar3_mul_halfModulus3_of_linearIndependent_domRestrict_of_le_card"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem finrank_inf_dualAnnihilator_le_of_le (S : Submodule K (V →ₗ[K] K)) [FiniteDimensional K S]
    {W W' : Submodule K V} (hW : W' ≤ W) {d : ℕ}
    (hd : ∀ (n : ℕ) (Λ : Fin n → (V →ₗ[K] K)), (∀ j, Λ j ∈ S) → (∀ j, ∀ x ∈ W', Λ j x = 0) →
      LinearIndependent K (fun j => (Λ j).domRestrict W) → n ≤ d) :
    finrank K ↥(S ⊓ W'.dualAnnihilator) ≤ finrank K ↥(S ⊓ W.dualAnnihilator) + d := by

  letI : AddCommGroup (V →ₗ[K] K) := inferInstance
  letI : AddCommGroup ↥(S ⊓ W'.dualAnnihilator) := inferInstance
  have _ := hW

  let N : Submodule K ↥(S ⊓ W'.dualAnnihilator) := W.dualAnnihilator.comap (S ⊓ W'.dualAnnihilator).subtype
  have hq := Submodule.finrank_quotient_add_finrank N
  have hN : finrank K ↥N ≤ finrank K ↥(S ⊓ W.dualAnnihilator) := by
    rw [← Submodule.finrank_map_subtype_eq (S ⊓ W'.dualAnnihilator) N]
    refine Submodule.finrank_mono fun Λ hΛ => ?_
    obtain ⟨Λ', hΛ', rfl⟩ := Submodule.mem_map.1 hΛ
    exact Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 Λ'.2).1, Submodule.mem_comap.1 hΛ'⟩

  have hQ : finrank K (↥(S ⊓ W'.dualAnnihilator) ⧸ N) ≤ d := by
    haveI : Module.Free K (↥(S ⊓ W'.dualAnnihilator) ⧸ N) := Module.Free.of_divisionRing K _
    let b := Module.finBasis K (↥(S ⊓ W'.dualAnnihilator) ⧸ N)
    choose p hp using fun j => Submodule.mkQ_surjective N (b j)
    refine hd _ (fun j => ((p j : ↥(S ⊓ W'.dualAnnihilator)) : V →ₗ[K] K))
      (fun j => (Submodule.mem_inf.1 (p j).2).1)
      (fun j x hx => (Submodule.mem_dualAnnihilator _).1 (Submodule.mem_inf.1 (p j).2).2 x hx) ?_
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hmem : (∑ k, c k • p k) ∈ N := by
      refine Submodule.mem_comap.2 ((Submodule.mem_dualAnnihilator _).2 fun w hw => ?_)
      have h0 := LinearMap.congr_fun hc ⟨w, hw⟩
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.domRestrict_apply, LinearMap.zero_apply] at h0
      simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.subtype_apply] using h0
    have hzero : (∑ k, c k • b k) = 0 := by
      have h1 : N.mkQ (∑ k, c k • p k) = 0 := (Submodule.Quotient.mk_eq_zero N).2 hmem
      simpa only [map_sum, map_smul, hp] using h1
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c hzero j
  omega

private theorem card_le_sum_of_linearIndependent_of_chain (G : Submodule K (V →ₗ[K] K)) (r : ℕ)
    (W : ℕ → Submodule K V) (h0 : W 0 = ⊤) (hr : W r = ⊥) (hanti : ∀ i < r, W (i + 1) ≤ W i) (d : ℕ → ℕ)
    (hd : ∀ i < r, ∀ (n : ℕ) (Λ : Fin n → (V →ₗ[K] K)), (∀ j, Λ j ∈ G) → (∀ j, ∀ x ∈ W (i + 1), Λ j x = 0) →
      LinearIndependent K (fun j => (Λ j).domRestrict (W i)) → n ≤ d i)
    (s : Finset (V →ₗ[K] K)) (hs : ∀ Λ ∈ s, Λ ∈ G)
    (hind : LinearIndependent K (fun Λ : ↥s => (Λ : V →ₗ[K] K))) :
    s.card ≤ ∑ i ∈ Finset.range r, d i := by
  classical
  set S : Submodule K (V →ₗ[K] K) := Submodule.span K (s : Set (V →ₗ[K] K)) with hS
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K s.finite_toSet
  have hSG : S ≤ G := Submodule.span_le.2 fun Λ hΛ => hs Λ hΛ
  have hcard : finrank K S = s.card := by
    have h := finrank_span_eq_card (R := K) hind
    rw [Subtype.range_coe_subtype, Finset.setOf_mem] at h
    rw [hS, h, Fintype.card_coe]
  have hstep : ∀ i, i ≤ r → finrank K ↥(S ⊓ (W i).dualAnnihilator) ≤ ∑ j ∈ Finset.range i, d j := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [h0, Submodule.dualAnnihilator_top]
    | succ i ih =>
      intro hi
      have hi' : i < r := hi
      refine (finrank_inf_dualAnnihilator_le_of_le S (hanti i hi') (d := d i) ?_).trans ?_
      · intro n Λ hΛS hΛW hli
        exact hd i hi' n Λ (fun j => hSG (hΛS j)) hΛW hli
      · rw [Finset.sum_range_succ]
        exact Nat.add_le_add_right (ih hi'.le) _
  have hr' := hstep r le_rfl
  rwa [hr, Submodule.dualAnnihilator_bot, inf_top_eq, hcard] at hr'

end LanglandsTunnell.CubicInduction

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (θ : (Fin 3 → (v.adicCompletion ℚ)ˣ) → ℂ)
    (s : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :
    (∀ Λ ∈ s, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f) →
    (∀ Λ ∈ s, ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v χ)),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ = θ a * Λ f) →
    (LinearIndependent ℂ (fun Λ : ↥s => (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))) →
    s.card ≤ {w : Equiv.Perm (Fin 3) |
      ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ, θ a = torusChar3 v (χ ∘ ⇑w) a * halfModulus3 v a}.ncard := by
  have hEVAL := le_one_of_linearIndependent_domRestrict_of_upperUnipotent3 v χ
  have hPROPER := eq_torusChar3_mul_halfModulus3_of_linearIndependent_domRestrict_of_le_card v χ
  have he : Function.Injective
      (![1, Equiv.swap 0 1, Equiv.swap 1 2, finRotate 3, (finRotate 3)⁻¹, Equiv.swap 0 2] :
        Fin 6 → Equiv.Perm (Fin 3)) := by
    decide
  intro hN hT hind
  classical

  set Z : Fin 7 → Set (LocalGL3 v) := ![∅,
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0},
      {g | cornerEntry v g * lowerMinor v g = 0},
      Set.univ] with hZ
  let W : Fin 7 → Submodule ℂ ↥(principalSeries3 v χ) := fun k =>
    Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ Z k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ))
  have hWk : ∀ k : Fin 7, W k = Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ Z k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)) := fun k => rfl
  have hZ0 : Z 0 = ∅ := by rw [hZ]; rfl
  have hZ1 : Z 1 = {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0} := by rw [hZ]; rfl
  have hZ2 : Z 2 = {g | cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0} := by rw [hZ]; rfl
  have hZ3 : Z 3 = {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0} := by rw [hZ]; rfl
  have hZ4 : Z 4 = {g | cornerEntry v g = 0} := by rw [hZ]; rfl
  have hZ5 : Z 5 = {g | cornerEntry v g * lowerMinor v g = 0} := by rw [hZ]; rfl
  have hZ6 : Z 6 = Set.univ := by rw [hZ]; rfl
  have hZ01 : Z 0 ⊆ Z 1 := by rw [hZ0]; exact Set.empty_subset _
  have hZ12 : Z 1 ⊆ Z 2 := by rw [hZ1, hZ2]; exact fun g hg => ⟨hg.1, hg.2.2⟩
  have hZ23 : Z 2 ⊆ Z 3 := by rw [hZ2, hZ3]; exact fun g hg => ⟨hg.1, by rw [hg.2, mul_zero]⟩
  have hZ34 : Z 3 ⊆ Z 4 := by rw [hZ3, hZ4]; exact fun g hg => hg.1
  have hZ45 : Z 4 ⊆ Z 5 := by
    rw [hZ4, hZ5]
    exact fun g (hg : cornerEntry v g = 0) => show cornerEntry v g * lowerMinor v g = 0 by rw [hg, zero_mul]
  have hZ56 : Z 5 ⊆ Z 6 := by rw [hZ6]; exact Set.subset_univ _

  let G : Submodule ℂ (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) :=
    { carrier := {Λ | (∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
          Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
            rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f) ∧
        (∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v χ)),
          Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
            rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ = θ a * Λ f)}
      add_mem' := by
        rintro Λ₁ Λ₂ ⟨h₁N, h₁T⟩ ⟨h₂N, h₂T⟩
        exact ⟨fun x y z f => by simp only [LinearMap.add_apply, h₁N, h₂N],
          fun a f => by simp only [LinearMap.add_apply, h₁T, h₂T, mul_add]⟩
      zero_mem' := ⟨fun x y z f => by simp, fun a f => by simp⟩
      smul_mem' := by
        rintro c Λ ⟨hcN, hcT⟩
        exact ⟨fun x y z f => by simp only [LinearMap.smul_apply, hcN],
          fun a f => by simp only [LinearMap.smul_apply, hcT, smul_eq_mul, mul_left_comm]⟩ }
  have hG : ∀ Λ ∈ s, Λ ∈ G := fun Λ hΛ => ⟨hN Λ hΛ, hT Λ hΛ⟩

  let e : Fin 6 → Equiv.Perm (Fin 3) :=
    ![1, Equiv.swap 0 1, Equiv.swap 1 2, finRotate 3, (finRotate 3)⁻¹, Equiv.swap 0 2]
  let P : Equiv.Perm (Fin 3) → Prop := fun w =>
    ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ, θ a = torusChar3 v (χ ∘ ⇑w) a * halfModulus3 v a
  let d : ℕ → ℕ := fun k => if h : k < 6 then (if P (e ⟨k, h⟩) then 1 else 0) else 0
  let W' : ℕ → Submodule ℂ ↥(principalSeries3 v χ) := fun k => if h : k < 7 then W ⟨k, h⟩ else ⊥
  have h0 : W' 0 = ⊤ := by
    have h00 : W' 0 = W 0 := dif_pos (by omega)
    rw [h00, hWk, hZ0]
    simp
  have hr : W' 6 = ⊥ := by
    have h66 : W' 6 = W 6 := dif_pos (by omega)
    rw [h66, hWk, hZ6, eq_bot_iff]
    intro f hf
    rw [Submodule.mem_comap, Submodule.mem_iInf] at hf
    have hf' : ∀ g, (f : LocalGL3 v → ℂ) g = 0 := fun g => by simpa using hf g
    rw [Submodule.mem_bot]
    exact Subtype.ext (funext fun g => by simpa using hf' g)
  have hanti : ∀ k < 6, W' (k + 1) ≤ W' k := by
    intro k hk
    have h1 : W' (k + 1) = W ⟨k + 1, by omega⟩ := dif_pos (by omega)
    have h2 : W' k = W ⟨k, by omega⟩ := dif_pos (by omega)
    rw [h1, h2, hWk, hWk]
    refine Submodule.comap_mono (biInf_mono ?_)
    interval_cases k
    · exact hZ01
    · exact hZ12
    · exact hZ23
    · exact hZ34
    · exact hZ45
    · exact hZ56
  have hd : ∀ k < 6, ∀ (n : ℕ) (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)), (∀ j, Λ j ∈ G) →
      (∀ j, ∀ x ∈ W' (k + 1), Λ j x = 0) →
      LinearIndependent ℂ (fun j => (Λ j).domRestrict (W' k)) → n ≤ d k := by
    intro k hk n Λ hΛG hkill hli
    have e1 : W' (k + 1) = W (⟨k, hk⟩ : Fin 6).succ := dif_pos (by omega)
    have e2 : W' k = W (⟨k, hk⟩ : Fin 6).castSucc := dif_pos (by omega)
    rw [e1] at hkill
    rw [e2] at hli
    have hNΛ := fun j => (hΛG j).1
    have hTΛ := fun j => (hΛG j).2
    by_cases hP : P (e ⟨k, hk⟩)
    · have hdk : d k = 1 := by simp only [d, dif_pos hk, if_pos hP]
      rw [hdk]
      exact hEVAL Z hZ W hWk ⟨k, hk⟩ n Λ hNΛ hkill hli
    · have hdk : d k = 0 := by simp only [d, dif_pos hk, if_neg hP]
      rw [hdk, Nat.le_zero]
      by_contra hn
      exact hP (hPROPER Z hZ W hWk θ ⟨k, hk⟩ n Λ hNΛ hTΛ hkill hli (Nat.one_le_iff_ne_zero.mpr hn))

  have hcard := card_le_sum_of_linearIndependent_of_chain G 6 W' h0 hr hanti d hd s hG hind
  have hsum : ∑ k ∈ Finset.range 6, d k = (Finset.univ.filter fun i : Fin 6 => P (e i)).card := by
    rw [Finset.card_filter, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [d, dif_pos i.isLt, Fin.eta]
  have hfin : {w : Equiv.Perm (Fin 3) | P w}.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  calc s.card ≤ ∑ k ∈ Finset.range 6, d k := hcard
    _ = (Finset.univ.filter fun i : Fin 6 => P (e i)).card := hsum
    _ = ((Finset.univ.filter fun i : Fin 6 => P (e i)).image e).card :=
        (Finset.card_image_of_injective _ he).symm
    _ ≤ hfin.toFinset.card := by
        refine Finset.card_le_card fun w hw => ?_
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨i, hi, rfl⟩ := hw
        simpa [Set.Finite.mem_toFinset] using hi

end S_LanglandsTunnell_CubicInduction_card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3 (solution)
