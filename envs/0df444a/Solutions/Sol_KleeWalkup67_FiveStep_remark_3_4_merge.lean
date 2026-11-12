-- Prove2me | solution 1 for KleeWalkup67.FiveStep.remark_3_4_merge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:57:31.156231+00:00
-- url     : https://prove2.me/submissions/effc03f3-03ff-45e6-a9cf-2ae79855dac6

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra
import Theorems.Thm_Hirsch_vertex_tight_rows_span

namespace Aux_KW67_remark_3_4_merge

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep

noncomputable def tightFinset {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ⟪a i, z⟫ = b i)

lemma mem_tightFinset {d n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin d)}
    {b : Fin n → ℝ} {z : EuclideanSpace ℝ (Fin d)} {i : Fin n} :
    i ∈ tightFinset a b z ↔ ⟪a i, z⟫ = b i := by
  classical
  simp [tightFinset]

lemma coe_tightFinset {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (tightFinset a b z : Set (Fin n)) = TightSet a b z := by
  ext i
  simp [mem_tightFinset, TightSet]

lemma card_tightFinset_eq_ncard {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    (tightFinset a b z).card = (TightSet a b z).ncard := by
  rw [← coe_tightFinset, Set.ncard_coe_finset]

lemma step_into_hpoly {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v u : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Hirsch.Hpoly a b)
    (hu : ∀ i ∈ tightFinset a b v, ⟪a i, u⟫ ≤ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → v + ε • u ∈ Hirsch.Hpoly a b := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < ⟪a i, u⟫)
  have hS_pos : ∀ i ∈ S, 0 < (b i - ⟪a i, v⟫) / ⟪a i, u⟫ := by
    intro i hi
    have hiu : 0 < ⟪a i, u⟫ := (Finset.mem_filter.mp hi).2
    have hnot : i ∉ tightFinset a b v := fun hm => by linarith [hu i hm]
    have hne : ⟪a i, v⟫ ≠ b i := by rwa [mem_tightFinset] at hnot
    have hlt : ⟪a i, v⟫ < b i := lt_of_le_of_ne (hv i) hne
    exact div_pos (sub_pos.mpr hlt) hiu
  by_cases hSne : S.Nonempty
  · let ε₀ : ℝ := S.inf' hSne (fun i => (b i - ⟪a i, v⟫) / ⟪a i, u⟫)
    have hε₀ : 0 < ε₀ := (Finset.lt_inf'_iff hSne).mpr hS_pos
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε hε_pos hε_le i
    rw [inner_add_right, real_inner_smul_right]
    rcases lt_or_ge 0 ⟪a i, u⟫ with hpos | hnonpos
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩
      have h1 : ε ≤ (b i - ⟪a i, v⟫) / ⟪a i, u⟫ := hε_le.trans (Finset.inf'_le _ hiS)
      have h2 : ε * ⟪a i, u⟫ ≤ b i - ⟪a i, v⟫ := (le_div_iff₀ hpos).mp h1
      linarith
    · have hmul : ε * ⟪a i, u⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_pos.le hnonpos
      linarith [hv i]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε_pos _ i
    rw [inner_add_right, real_inner_smul_right]
    have hnonpos : ⟪a i, u⟫ ≤ 0 := by
      by_contra hlt
      push Not at hlt
      exact hSne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩⟩
    have hmul : ε * ⟪a i, u⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε_pos.le hnonpos
    linarith [hv i]

noncomputable def tightLinearMap {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (tightFinset a b v → ℝ) where
  toFun w i := ⟪a i.1, w⟫
  map_add' x y := by ext i; simp [inner_add_right]
  map_smul' r x := by ext i; simp [real_inner_smul_right]

noncomputable def tightEquiv {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard : (TightSet a b v).ncard = d) :
    EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (tightFinset a b v → ℝ) := by
  let f := tightLinearMap a b v
  have hinj : Function.Injective f := by
    intro x y hxy
    have h0 : x - y = 0 := by
      refine Hirsch.vertex_tight_rows_span d n a b v hv (x - y) ?_
      intro j hj
      have hfj := congr_fun hxy ⟨j, mem_tightFinset.mpr hj⟩
      dsimp [f, tightLinearMap] at hfj
      rw [inner_sub_right, hfj, sub_self]
    exact sub_eq_zero.mp h0
  have hcard_fin : (tightFinset a b v).card = d := by
    rw [card_tightFinset_eq_ncard, hcard]
  have hfr_dom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have hfr_cod : Module.finrank ℝ (tightFinset a b v → ℝ) = d := by
    simp [hcard_fin]
  have hker : Module.finrank ℝ (LinearMap.ker f) = 0 :=
    Submodule.finrank_eq_zero.mpr (LinearMap.ker_eq_bot.mpr hinj)
  have hrng : Module.finrank ℝ (LinearMap.range f) =
      Module.finrank ℝ (tightFinset a b v → ℝ) := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    omega
  have hsurj : Function.Surjective f :=
    LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hrng)
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

def zeroOnSubmodule {n : ℕ} (T J : Finset (Fin n)) : Submodule ℝ (T → ℝ) where
  carrier := {f | ∀ i : T, i.1 ∈ J → f i = 0}
  add_mem' ha hb i hi := by simp [ha i hi, hb i hi]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf i hi := by simp [hf i hi]

noncomputable def zeroOnEquivSdiff {n : ℕ} (T J : Finset (Fin n)) :
    zeroOnSubmodule T J ≃ₗ[ℝ] ((T \ J : Finset (Fin n)) → ℝ) := by
  classical
  refine
    { toFun := fun f k => f.1 ⟨k.1, (Finset.mem_sdiff.mp k.2).1⟩
      invFun := fun g =>
        ⟨fun i => if hi : i.1 ∈ J then 0 else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, hi⟩⟩,
          fun i hi => dif_pos hi⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    ext i
    by_cases hi : i.1 ∈ J
    · simp [hi, f.2 i hi]
    · simp [hi]
  · intro g
    ext k
    have hk : k.1 ∉ J := (Finset.mem_sdiff.mp k.2).2
    simp [hk]

lemma dim_faceOf_at_simple_vertex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hcard : (TightSet a b v).ncard = d)
    (J : Finset (Fin n)) (hvJ : v ∈ faceOf a b J) :
    J ⊆ tightFinset a b v ∧ dim (faceOf a b J) = d - J.card := by
  classical
  have hJT : J ⊆ tightFinset a b v := fun i hi => mem_tightFinset.mpr (hvJ.2 i hi)
  refine ⟨hJT, ?_⟩
  let E := tightEquiv a b hv hcard
  let M := zeroOnSubmodule (tightFinset a b v) J
  have hdir : (affineSpan ℝ (faceOf a b J)).direction = M.comap E.toLinearMap := by
    apply le_antisymm
    · rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro w ⟨z₁, hz₁, z₂, hz₂, rfl⟩
      intro i hi
      change ⟪a i.1, z₁ - z₂⟫ = 0
      rw [inner_sub_right, hz₁.2 i.1 hi, hz₂.2 i.1 hi, sub_self]
    · intro w hw
      rw [direction_affineSpan]
      let g₀ : tightFinset a b v → ℝ := fun k => if k.1 ∈ J then 0 else -1 - |E w k|
      let g₁ : tightFinset a b v → ℝ := g₀ + E w
      let u₀ := E.symm g₀
      let u₁ := E.symm g₁
      have hu₀_le : ∀ i ∈ tightFinset a b v, ⟪a i, u₀⟫ ≤ 0 := by
        intro i hi
        have heq : ⟪a i, u₀⟫ = g₀ ⟨i, hi⟩ := by
          change E u₀ ⟨i, hi⟩ = g₀ ⟨i, hi⟩
          simp [u₀]
        rw [heq]
        dsimp [g₀]
        split_ifs
        · exact le_rfl
        · linarith [abs_nonneg (E w ⟨i, hi⟩)]
      have hu₁_le : ∀ i ∈ tightFinset a b v, ⟪a i, u₁⟫ ≤ 0 := by
        intro i hi
        have heq : ⟪a i, u₁⟫ = g₁ ⟨i, hi⟩ := by
          change E u₁ ⟨i, hi⟩ = g₁ ⟨i, hi⟩
          simp [u₁]
        rw [heq]
        dsimp [g₁, g₀]
        split_ifs with hJ
        · have hw0 : E w ⟨i, hi⟩ = 0 := hw ⟨i, hi⟩ hJ
          linarith
        · linarith [le_abs_self (E w ⟨i, hi⟩)]
      obtain ⟨ε₀, hε₀_pos, hε₀⟩ := step_into_hpoly a b hv.1 hu₀_le
      obtain ⟨ε₁, hε₁_pos, hε₁⟩ := step_into_hpoly a b hv.1 hu₁_le
      let ε := min ε₀ ε₁
      have hε_pos : 0 < ε := lt_min hε₀_pos hε₁_pos
      have hz₀ : v + ε • u₀ ∈ faceOf a b J := by
        refine ⟨hε₀ ε hε_pos (min_le_left _ _), ?_⟩
        intro i hi
        have hiT : i ∈ tightFinset a b v := hJT hi
        have heq : ⟪a i, u₀⟫ = g₀ ⟨i, hiT⟩ := by
          change E u₀ ⟨i, hiT⟩ = g₀ ⟨i, hiT⟩
          simp [u₀]
        rw [inner_add_right, real_inner_smul_right, hvJ.2 i hi, heq]
        simp [g₀, hi]
      have hz₁ : v + ε • u₁ ∈ faceOf a b J := by
        refine ⟨hε₁ ε hε_pos (min_le_right _ _), ?_⟩
        intro i hi
        have hiT : i ∈ tightFinset a b v := hJT hi
        have heq : ⟪a i, u₁⟫ = g₁ ⟨i, hiT⟩ := by
          change E u₁ ⟨i, hiT⟩ = g₁ ⟨i, hiT⟩
          simp [u₁]
        have hw0 : E w ⟨i, hiT⟩ = 0 := hw ⟨i, hiT⟩ hi
        rw [inner_add_right, real_inner_smul_right, hvJ.2 i hi, heq]
        simp [g₁, g₀, hi, hw0]
      have hmem : (v + ε • u₁) -ᵥ (v + ε • u₀) ∈ vectorSpan ℝ (faceOf a b J) :=
        vsub_mem_vectorSpan ℝ hz₁ hz₀
      have hdiff : (v + ε • u₁) -ᵥ (v + ε • u₀) = ε • w := by
        have hu10 : u₁ - u₀ = w := by
          dsimp [u₁, u₀, g₁]
          rw [map_add, add_sub_cancel_left, E.symm_apply_apply]
        calc (v + ε • u₁) - (v + ε • u₀)
            = ε • (u₁ - u₀) := by module
          _ = ε • w := by rw [hu10]
      rw [hdiff] at hmem
      have hsmul := Submodule.smul_mem (vectorSpan ℝ (faceOf a b J)) ε⁻¹ hmem
      rwa [inv_smul_smul₀ (ne_of_gt hε_pos)] at hsmul
  unfold dim
  rw [hdir]
  let e1 : M.comap E.toLinearMap ≃ₗ[ℝ] M :=
    { toFun := fun x => ⟨E x.1, x.2⟩
      invFun := fun y => ⟨E.symm y.1, by simp [M, y.2]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  change Module.finrank ℝ (M.comap E.toLinearMap) = d - J.card
  rw [e1.finrank_eq, (zeroOnEquivSdiff (tightFinset a b v) J).finrank_eq,
    Module.finrank_pi, Fintype.card_coe]
  have hcard_T : (tightFinset a b v).card = d := by
    rw [card_tightFinset_eq_ncard, hcard]
  have h := Finset.card_sdiff_add_card_eq_card hJT
  omega

lemma nonempty_faceOf_has_vertex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) {v₀ : EuclideanSpace ℝ (Fin d)}
    (hv₀ : v₀ ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (I : Finset (Fin n)) (hne : (faceOf a b I).Nonempty) :
    ∃ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b), v ∈ faceOf a b I := by
  classical
  have hinj_all : ∀ e : EuclideanSpace ℝ (Fin d), (∀ j : Fin n, ⟪a j, e⟫ = 0) → e = 0 := by
    intro e he
    exact Hirsch.vertex_tight_rows_span d n a b v₀ hv₀ e (fun j _ => he j)
  suffices hind : ∀ (m : ℕ) (z : EuclideanSpace ℝ (Fin d)),
      z ∈ faceOf a b I → n - (tightFinset a b z).card ≤ m →
      ∃ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b), v ∈ faceOf a b I by
    obtain ⟨z, hz⟩ := hne
    exact hind (n - (tightFinset a b z).card) z hz le_rfl
  intro m
  induction m with
  | zero =>
      intro z hz hm
      by_cases hspan : ∀ e : EuclideanSpace ℝ (Fin d),
          (∀ j ∈ tightFinset a b z, ⟪a j, e⟫ = 0) → e = 0
      · refine ⟨z, ⟨hz.1, ?_⟩, hz⟩
        rintro x₁ hx₁ x₂ hx₂ ⟨p, q, hp, hq, hpq, hcomb⟩
        have hxz : x₁ - z = 0 := by
          refine hspan (x₁ - z) ?_
          intro j hj
          have hjz : ⟪a j, z⟫ = b j := mem_tightFinset.mp hj
          have hj1 : ⟪a j, x₁⟫ ≤ b j := hx₁ j
          have hj2 : ⟪a j, x₂⟫ ≤ b j := hx₂ j
          have hlin : p * ⟪a j, x₁⟫ + q * ⟪a j, x₂⟫ = b j := by
            rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb, hjz]
          have heq1 : ⟪a j, x₁⟫ = b j := by
            by_contra hne1
            have hlt1 : ⟪a j, x₁⟫ < b j := lt_of_le_of_ne hj1 hne1
            have hm1 : p * ⟪a j, x₁⟫ < p * b j := mul_lt_mul_of_pos_left hlt1 hp
            have hm2 : q * ⟪a j, x₂⟫ ≤ q * b j := mul_le_mul_of_nonneg_left hj2 hq.le
            have hm3 : p * b j + q * b j = b j := by rw [← add_mul, hpq, one_mul]
            linarith
          rw [inner_sub_right, heq1, hjz, sub_self]
        exact sub_eq_zero.mp hxz
      · push Not at hspan
        obtain ⟨e, heT, he_ne⟩ := hspan
        have hex : ∃ j : Fin n, ⟪a j, e⟫ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact he_ne (hinj_all e hall)
        obtain ⟨j₀, hj₀⟩ := hex
        have hcard_le : (tightFinset a b z).card ≤ n := by
          simpa using Finset.card_le_univ (tightFinset a b z)
        have hcard_eq : (tightFinset a b z).card = n := by omega
        have huniv : tightFinset a b z = Finset.univ :=
          Finset.eq_univ_of_card _ (by simpa using hcard_eq)
        exact absurd (heT j₀ (by simp [huniv])) hj₀
  | succ m ih =>
      intro z hz hm
      by_cases hspan : ∀ e : EuclideanSpace ℝ (Fin d),
          (∀ j ∈ tightFinset a b z, ⟪a j, e⟫ = 0) → e = 0
      · refine ⟨z, ⟨hz.1, ?_⟩, hz⟩
        rintro x₁ hx₁ x₂ hx₂ ⟨p, q, hp, hq, hpq, hcomb⟩
        have hxz : x₁ - z = 0 := by
          refine hspan (x₁ - z) ?_
          intro j hj
          have hjz : ⟪a j, z⟫ = b j := mem_tightFinset.mp hj
          have hj1 : ⟪a j, x₁⟫ ≤ b j := hx₁ j
          have hj2 : ⟪a j, x₂⟫ ≤ b j := hx₂ j
          have hlin : p * ⟪a j, x₁⟫ + q * ⟪a j, x₂⟫ = b j := by
            rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hcomb, hjz]
          have heq1 : ⟪a j, x₁⟫ = b j := by
            by_contra hne1
            have hlt1 : ⟪a j, x₁⟫ < b j := lt_of_le_of_ne hj1 hne1
            have hm1 : p * ⟪a j, x₁⟫ < p * b j := mul_lt_mul_of_pos_left hlt1 hp
            have hm2 : q * ⟪a j, x₂⟫ ≤ q * b j := mul_le_mul_of_nonneg_left hj2 hq.le
            have hm3 : p * b j + q * b j = b j := by rw [← add_mul, hpq, one_mul]
            linarith
          rw [inner_sub_right, heq1, hjz, sub_self]
        exact sub_eq_zero.mp hxz
      · push Not at hspan
        obtain ⟨e₀, he₀T, he₀_ne⟩ := hspan
        have hex : ∃ j : Fin n, ⟪a j, e₀⟫ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact he₀_ne (hinj_all e₀ hall)
        obtain ⟨j₀, hj₀⟩ := hex
        let e : EuclideanSpace ℝ (Fin d) := if 0 < ⟪a j₀, e₀⟫ then e₀ else -e₀
        have heT : ∀ j ∈ tightFinset a b z, ⟪a j, e⟫ = 0 := by
          intro j hj
          dsimp [e]
          split_ifs
          · exact he₀T j hj
          · rw [inner_neg_right, he₀T j hj, neg_zero]
        have hj₀_pos : 0 < ⟪a j₀, e⟫ := by
          dsimp [e]
          split_ifs with hpos
          · exact hpos
          · rw [inner_neg_right]
            rcases lt_trichotomy 0 ⟪a j₀, e₀⟫ with h1 | h1 | h1
            · exact absurd h1 hpos
            · exact absurd h1.symm hj₀
            · linarith
        let S : Finset (Fin n) := Finset.univ.filter (fun j => 0 < ⟪a j, e⟫)
        have hj₀S : j₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀_pos⟩
        obtain ⟨jstar, hjstarS, hjstar_min⟩ :=
          Finset.exists_min_image S (fun j => (b j - ⟪a j, z⟫) / ⟪a j, e⟫) ⟨j₀, hj₀S⟩
        have hjstar_e : 0 < ⟪a jstar, e⟫ := (Finset.mem_filter.mp hjstarS).2
        have hjstar_notT : jstar ∉ tightFinset a b z := fun hm => by
          linarith [heT jstar hm]
        have hjstar_lt : ⟪a jstar, z⟫ < b jstar :=
          lt_of_le_of_ne (hz.1 jstar) (by rwa [mem_tightFinset] at hjstar_notT)
        let tstar : ℝ := (b jstar - ⟪a jstar, z⟫) / ⟪a jstar, e⟫
        have htstar_pos : 0 < tstar := div_pos (sub_pos.mpr hjstar_lt) hjstar_e
        let z' := z + tstar • e
        have hz' : z' ∈ faceOf a b I := by
          refine ⟨?_, ?_⟩
          · intro j
            dsimp [z']
            rw [inner_add_right, real_inner_smul_right]
            rcases lt_or_ge 0 ⟪a j, e⟫ with hjp | hjn
            · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjp⟩
              have hle : tstar ≤ (b j - ⟪a j, z⟫) / ⟪a j, e⟫ := hjstar_min j hjS
              have hmul : tstar * ⟪a j, e⟫ ≤ b j - ⟪a j, z⟫ := (le_div_iff₀ hjp).mp hle
              linarith
            · have hmul : tstar * ⟪a j, e⟫ ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos htstar_pos.le hjn
              linarith [hz.1 j]
          · intro i hi
            have hiT : i ∈ tightFinset a b z := mem_tightFinset.mpr (hz.2 i hi)
            dsimp [z']
            rw [inner_add_right, real_inner_smul_right, hz.2 i hi, heT i hiT, mul_zero, add_zero]
        have hsub : tightFinset a b z ⊆ tightFinset a b z' := by
          intro j hj
          rw [mem_tightFinset] at hj ⊢
          dsimp [z']
          rw [inner_add_right, real_inner_smul_right, hj, heT j (mem_tightFinset.mpr hj),
            mul_zero, add_zero]
        have hjstar_in : jstar ∈ tightFinset a b z' := by
          rw [mem_tightFinset]
          dsimp [z', tstar]
          rw [inner_add_right, real_inner_smul_right, div_mul_cancel₀ _ (ne_of_gt hjstar_e)]
          ring
        have hssub : tightFinset a b z ⊂ tightFinset a b z' :=
          Finset.ssubset_iff_of_subset hsub |>.mpr ⟨jstar, hjstar_in, hjstar_notT⟩
        have hlt_card : (tightFinset a b z).card < (tightFinset a b z').card :=
          Finset.card_lt_card hssub
        have hcard_le : (tightFinset a b z').card ≤ n := by
          simpa using Finset.card_le_univ (tightFinset a b z')
        exact ih z' hz' (by omega)

lemma list_get_mid₁ : ∀ (l₁ l₂ : List ℕ) (p q : ℕ) (h : l₁.length < (l₁ ++ p :: q :: l₂).length),
    (l₁ ++ p :: q :: l₂).get ⟨l₁.length, h⟩ = p
  | [], _, _, _, _ => rfl
  | _ :: tl, l₂, p, q, _ => list_get_mid₁ tl l₂ p q (by simp)

lemma list_get_mid₂ : ∀ (l₁ l₂ : List ℕ) (p q : ℕ)
    (h : l₁.length + 1 < (l₁ ++ p :: q :: l₂).length),
    (l₁ ++ p :: q :: l₂).get ⟨l₁.length + 1, h⟩ = q
  | [], _, _, _, _ => rfl
  | _ :: tl, l₂, p, q, _ => list_get_mid₂ tl l₂ p q (by simp)

lemma list_get_new_mid : ∀ (l₁ l₂ : List ℕ) (r : ℕ) (h : l₁.length < (l₁ ++ r :: l₂).length),
    (l₁ ++ r :: l₂).get ⟨l₁.length, h⟩ = r
  | [], _, _, _ => rfl
  | _ :: tl, l₂, r, _ => list_get_new_mid tl l₂ r (by simp)

lemma list_get_left : ∀ (l₁ s₁ s₂ : List ℕ) (k : ℕ) (_ : k < l₁.length)
    (h₁ : k < (l₁ ++ s₁).length) (h₂ : k < (l₁ ++ s₂).length),
    (l₁ ++ s₁).get ⟨k, h₁⟩ = (l₁ ++ s₂).get ⟨k, h₂⟩
  | [], _, _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, _, _, 0, _, _, _ => rfl
  | _ :: tl, s₁, s₂, k + 1, hk, h₁, h₂ =>
      list_get_left tl s₁ s₂ k (Nat.lt_of_succ_lt_succ hk) (by simp at h₁ ⊢; omega)
        (by simp at h₂ ⊢; omega)

lemma list_get_right : ∀ (l₁ l₂ : List ℕ) (p q r m : ℕ)
    (h₁ : l₁.length + 2 + m < (l₁ ++ p :: q :: l₂).length)
    (h₂ : l₁.length + 1 + m < (l₁ ++ r :: l₂).length),
    (l₁ ++ p :: q :: l₂).get ⟨l₁.length + 2 + m, h₁⟩ =
      (l₁ ++ r :: l₂).get ⟨l₁.length + 1 + m, h₂⟩
  | [], l₂, p, q, r, m, h₁, h₂ => by
      simp only [List.nil_append, List.length_nil, Nat.zero_add, List.get_eq_getElem]
      have e1 : 2 + m = m + 1 + 1 := by omega
      have e2 : 1 + m = m + 1 := by omega
      simp [e1, e2]
  | _ :: tl, l₂, p, q, r, m, h₁, h₂ => by
      have e1 : (tl.length + 1) + 2 + m = (tl.length + 2 + m) + 1 := by omega
      have e2 : (tl.length + 1) + 1 + m = (tl.length + 1 + m) + 1 := by omega
      have h₁' : tl.length + 2 + m < (tl ++ p :: q :: l₂).length := by simp at h₁ ⊢; omega
      have h₂' : tl.length + 1 + m < (tl ++ r :: l₂).length := by simp at h₂ ⊢; omega
      have ih := list_get_right tl l₂ p q r m h₁' h₂'
      simp only [List.get_eq_getElem, List.cons_append] at ih ⊢
      simpa [e1, e2] using ih

end Aux_KW67_remark_3_4_merge

open scoped RealInnerProductSpace
open KleeWalkup67.FiveStep Aux_KW67_remark_3_4_merge

theorem solution {d : ℕ}
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hD : IsDantzigFigure a b x y) (hS : IsSimple a b)
    (l₁ l₂ : List ℕ) (p q : ℕ) (hpq : p + q ≤ d)
    (hpath : IsFacialPath a b (l₁ ++ p :: q :: l₂) x y) :
    IsFacialPath a b (l₁ ++ (p + q) :: l₂) x y := by
  classical
  obtain ⟨K, hK_face, hK_adj, hlen₁, hx0, hylast⟩ := hpath
  have hip_lt : l₁.length < (l₁ ++ p :: q :: l₂).length := by simp
  have hiq_lt : l₁.length + 1 < (l₁ ++ p :: q :: l₂).length := by simp
  let ip : Fin (l₁ ++ p :: q :: l₂).length := ⟨l₁.length, hip_lt⟩
  let iq : Fin (l₁ ++ p :: q :: l₂).length := ⟨l₁.length + 1, hiq_lt⟩
  obtain ⟨⟨_, I₁, hKI₁⟩, hdim_p⟩ := hK_face ip
  obtain ⟨⟨_, I₂, hKI₂⟩, hdim_q⟩ := hK_face iq
  rw [list_get_mid₁ l₁ l₂ p q hip_lt] at hdim_p
  rw [list_get_mid₂ l₁ l₂ p q hiq_lt] at hdim_q
  have hinter_ne : (K ip ∩ K iq).Nonempty := hK_adj ip iq rfl
  have hinter_eq : K ip ∩ K iq = faceOf a b (I₁ ∪ I₂) := by
    ext z
    simp only [Set.mem_inter_iff, hKI₁, hKI₂, faceOf, Finset.mem_union]
    constructor
    · rintro ⟨⟨hzP, h1⟩, ⟨_, h2⟩⟩
      exact ⟨hzP, fun i hi => hi.elim (h1 i) (h2 i)⟩
    · rintro ⟨hzP, h12⟩
      exact ⟨⟨hzP, fun i hi => h12 i (Or.inl hi)⟩, ⟨hzP, fun i hi => h12 i (Or.inr hi)⟩⟩
  rw [hinter_eq] at hinter_ne
  obtain ⟨v, hv_ext, hv_mem⟩ := nonempty_faceOf_has_vertex a b hD.2.1 (I₁ ∪ I₂) hinter_ne
  have hv1 : v ∈ faceOf a b I₁ := ⟨hv_mem.1, fun i hi => hv_mem.2 i (Finset.mem_union_left _ hi)⟩
  have hv2 : v ∈ faceOf a b I₂ := ⟨hv_mem.1, fun i hi => hv_mem.2 i (Finset.mem_union_right _ hi)⟩
  have hv_card : (TightSet a b v).ncard = d := hS.2 v hv_ext
  obtain ⟨hI₁T, hdim₁⟩ := dim_faceOf_at_simple_vertex a b hv_ext hv_card I₁ hv1
  obtain ⟨hI₂T, hdim₂⟩ := dim_faceOf_at_simple_vertex a b hv_ext hv_card I₂ hv2
  rw [← hKI₁, hdim_p] at hdim₁
  rw [← hKI₂, hdim_q] at hdim₂
  have hTv_card : (tightFinset a b v).card = d := by
    rw [card_tightFinset_eq_ncard, hv_card]
  have hI₁_le : I₁.card ≤ d := (Finset.card_le_card hI₁T).trans_eq hTv_card
  have hI₂_le : I₂.card ≤ d := (Finset.card_le_card hI₂T).trans_eq hTv_card
  have hunion_le : (I₁ ∪ I₂).card ≤ d :=
    (Finset.card_le_card (Finset.union_subset hI₁T hI₂T)).trans_eq hTv_card
  have hcard_inter : d - (p + q) ≤ (I₁ ∩ I₂).card := by
    have hu := Finset.card_union_add_card_inter I₁ I₂
    omega
  obtain ⟨J, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq hcard_inter
  let Kstar : Set (EuclideanSpace ℝ (Fin d)) := faceOf a b J
  have hJ_I₁ : J ⊆ I₁ := hJ_sub.trans Finset.inter_subset_left
  have hJ_I₂ : J ⊆ I₂ := hJ_sub.trans Finset.inter_subset_right
  have hsub₁ : K ip ⊆ Kstar := by
    rw [hKI₁]
    intro z hz
    exact ⟨hz.1, fun i hi => hz.2 i (hJ_I₁ hi)⟩
  have hsub₂ : K iq ⊆ Kstar := by
    rw [hKI₂]
    intro z hz
    exact ⟨hz.1, fun i hi => hz.2 i (hJ_I₂ hi)⟩
  have hv_Kstar : v ∈ Kstar := hsub₁ (hKI₁ ▸ hv1)
  have hKstar_face : IsFace a b Kstar := ⟨⟨v, hv_Kstar⟩, J, rfl⟩
  have hKstar_dim : dim Kstar = p + q := by
    have hd := (dim_faceOf_at_simple_vertex a b hv_ext hv_card J hv_Kstar).2
    change dim (faceOf a b J) = p + q
    omega
  have hlen_eq₁ : (l₁ ++ p :: q :: l₂).length = l₁.length + 2 + l₂.length := by simp; omega
  have hlen_eq₂ : (l₁ ++ (p + q) :: l₂).length = l₁.length + 1 + l₂.length := by simp; omega
  let K' : Fin (l₁ ++ (p + q) :: l₂).length → Set (EuclideanSpace ℝ (Fin d)) := fun idx =>
    if hlt : idx.1 < l₁.length then
      K ⟨idx.1, by have := idx.2; omega⟩
    else if idx.1 = l₁.length then
      Kstar
    else
      K ⟨idx.1 + 1, by have := idx.2; omega⟩
  refine ⟨K', ?_, ?_, ?_⟩
  · intro idx
    dsimp [K']
    split_ifs with hlt heq
    · obtain ⟨hf, hd⟩ := hK_face ⟨idx.1, by have := idx.2; omega⟩
      refine ⟨hf, ?_⟩
      rw [hd]
      exact list_get_left l₁ (p :: q :: l₂) ((p + q) :: l₂) idx.1 hlt _ idx.2
    · refine ⟨hKstar_face, ?_⟩
      rcases idx with ⟨val, hval⟩
      dsimp at heq
      subst heq
      rw [hKstar_dim]
      exact (list_get_new_mid l₁ l₂ (p + q) hval).symm
    · have hidx2 := idx.2
      obtain ⟨hf, hd⟩ := hK_face ⟨idx.1 + 1, by omega⟩
      refine ⟨hf, ?_⟩
      rw [hd]
      obtain ⟨m, hm⟩ : ∃ m, idx.1 = l₁.length + 1 + m := ⟨idx.1 - (l₁.length + 1), by omega⟩
      rcases idx with ⟨val, hval⟩
      dsimp at hm hidx2 ⊢
      subst hm
      have h1 : l₁.length + 2 + m < (l₁ ++ p :: q :: l₂).length := by omega
      have h2 : l₁.length + 1 + m < (l₁ ++ (p + q) :: l₂).length := by omega
      have hget := list_get_right l₁ l₂ p q (p + q) m h1 h2
      have heq_idx : l₁.length + 1 + m + 1 = l₁.length + 2 + m := by omega
      simp only [List.get_eq_getElem] at hget ⊢
      simp only [heq_idx]
      exact hget
  · intro i j hij
    have hi2 := i.2
    have hj2 := j.2
    dsimp [K']
    split_ifs with hi_lt hi_eq hj_lt hj_eq <;> try omega
    · exact hK_adj ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hij
    · have hne := hK_adj ⟨i.1, by omega⟩ ip (by dsimp [ip]; omega)
      exact hne.mono (Set.inter_subset_inter_right _ hsub₁)
    · have hne := hK_adj iq ⟨j.1 + 1, by omega⟩ (by dsimp [iq]; omega)
      exact hne.mono (Set.inter_subset_inter_left _ hsub₂)
    · exact hK_adj ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩ (by dsimp; omega)
  · have hlen₂ : 0 < (l₁ ++ (p + q) :: l₂).length := by omega
    refine ⟨hlen₂, ?_, ?_⟩
    · dsimp only [K']
      by_cases h0 : 0 < l₁.length
      · rw [dif_pos h0]
        exact hx0
      · rw [dif_neg h0, if_pos (by omega)]
        have heq_ip : (⟨0, hlen₁⟩ : Fin (l₁ ++ p :: q :: l₂).length) = ip := by
          ext; dsimp [ip]; omega
        rw [heq_ip] at hx0
        exact hsub₁ hx0
    · dsimp [K']
      split_ifs with hlast_lt hlast_eq
      · omega
      · have heq_iq : (⟨(l₁ ++ p :: q :: l₂).length - 1,
            Nat.sub_lt hlen₁ Nat.one_pos⟩ : Fin (l₁ ++ p :: q :: l₂).length) = iq := by
          ext; dsimp [iq]; omega
        rw [heq_iq] at hylast
        exact hsub₂ hylast
      · have heq_last : (⟨(l₁ ++ (p + q) :: l₂).length - 1 + 1, by omega⟩ :
            Fin (l₁ ++ p :: q :: l₂).length) =
            ⟨(l₁ ++ p :: q :: l₂).length - 1, Nat.sub_lt hlen₁ Nat.one_pos⟩ := by
          ext; dsimp; omega
        rw [heq_last]
        exact hylast
