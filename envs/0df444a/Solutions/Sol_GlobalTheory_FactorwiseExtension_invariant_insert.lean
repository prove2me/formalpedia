-- Prove2me | solution 1 for GlobalTheory.FactorwiseExtension.invariant_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:36.21779+00:00
-- url     : https://prove2.me/submissions/b952835b-1344-466b-93ab-2542482b559c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant
import Theorems.Thm_GlobalTheory_FactorwiseExtension_toLinearMap_congr
import Theorems.Thm_GlobalTheory_FactorwiseExtension_toLinearMap_update_add
import Theorems.Thm_GlobalTheory_FactorwiseExtension_toLinearMap_update_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory GlobalTheory.FactorwiseExtension
variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.FactorwiseExtension
theorem _root_.solution (A B : ∀ τ, Submodule ℂ (H τ)) (hAB : ∀ τ, A τ ≤ B τ)
    (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E)))
    (hRk : ∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) (hRg : ∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ)
    (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E))
    (hC : ∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ)
    (hext : ∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x)
    (huniq : ∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0)
    (hpostC : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ')
    (hbs : ∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') →
      (∀ a ∈ A τ', F.flip a ∈ C τ) → ∀ b ∈ B τ', F.flip b ∈ C τ)
    (T₀ : MultilinearMap ℂ H E) (s : Finset ι) (τ₀ : ι) (hτ₀ : τ₀ ∉ s) (T : MultilinearMap ℂ H E)
    (hT : Invariant A B Rk Rg C T₀ s T) : ∃ T', Invariant A B Rk Rg C T₀ (insert τ₀ s) T' := by
  obtain ⟨hTa, hTb, hTc⟩ := hT
  set D' := piecewiseSubmodule A B (insert τ₀ s) with hD'
  have hD'0 : D' τ₀ = B τ₀ := if_pos (Finset.mem_insert_self τ₀ s)
  have hBD' : ∀ x ∈ B τ₀, x ∈ D' τ₀ := fun x hx => by rw [hD'0]; exact hx
  have hD'B : ∀ x ∈ D' τ₀, x ∈ B τ₀ := fun x hx => by rw [← hD'0]; exact hx
  have hD'ne : ∀ τ, τ ≠ τ₀ → D' τ = piecewiseSubmodule A B s τ := by
    intro τ hτ
    simp only [hD', piecewiseSubmodule, Finset.mem_insert, hτ, false_or]
  have hAD' : ∀ τ, ∀ x ∈ A τ, x ∈ D' τ := by
    intro τ x hx
    simp only [hD', piecewiseSubmodule]
    split_ifs
    · exact hAB τ hx
    · exact hx
  have hD0 : piecewiseSubmodule A B s τ₀ = A τ₀ := if_neg hτ₀

  have hret := fun τ => (D' τ).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  choose g hg using hret
  let R : ∀ τ, H τ →ₗ[ℂ] H τ := fun τ => (D' τ).subtype ∘ₗ g τ
  have hRmem : ∀ τ x, R τ x ∈ D' τ := fun τ x => (g τ x).2
  have hRid : ∀ τ, ∀ x ∈ D' τ, R τ x = x := by
    intro τ x hx
    have := congrArg (fun f => ((f ⟨x, hx⟩ : D' τ) : H τ)) (hg τ)
    simpa [R] using this

  have goodL : ∀ w : ∀ τ, H τ, (∀ τ', τ' ≠ τ₀ → w τ' ∈ D' τ') →
      ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, T.toLinearMap w τ₀ (r.1 x) = r.2 (T.toLinearMap w τ₀ x) := by
    intro w hw r hr x hx
    simp only [MultilinearMap.toLinearMap_apply]
    exact hTb τ₀ hτ₀ w (fun τ' h => by rw [← hD'ne τ' h]; exact hw τ' h) r hr x hx
  choose! Ext hExtC hExtG hExtA using hext τ₀
  have ExtAdd : ∀ L₁ L₂ : H τ₀ →ₗ[ℂ] E, (∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, L₁ (r.1 x) = r.2 (L₁ x)) →
      (∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, L₂ (r.1 x) = r.2 (L₂ x)) →
      ∀ b ∈ B τ₀, Ext (L₁ + L₂) b = Ext L₁ b + Ext L₂ b := by
    intro L₁ L₂ h₁ h₂ b hb
    have h₁₂ : ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, (L₁ + L₂) (r.1 x) = r.2 ((L₁ + L₂) x) := by
      intro r hr x hx
      simp only [LinearMap.add_apply, map_add, h₁ r hr x hx, h₂ r hr x hx]
    have := huniq τ₀ (Ext (L₁ + L₂) - Ext L₁ - Ext L₂)
      (sub_mem (sub_mem (hExtC _ h₁₂) (hExtC _ h₁)) (hExtC _ h₂))
      (by
        intro x hx
        simp only [LinearMap.sub_apply, LinearMap.add_apply, hExtA _ h₁₂ x hx, hExtA _ h₁ x hx,
          hExtA _ h₂ x hx]
        abel) b hb
    simp only [LinearMap.sub_apply] at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  have ExtSmul : ∀ (c : ℂ) (L : H τ₀ →ₗ[ℂ] E), (∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, L (r.1 x) = r.2 (L x)) →
      ∀ b ∈ B τ₀, Ext (c • L) b = c • Ext L b := by
    intro c L h b hb
    have hc : ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀, (c • L) (r.1 x) = r.2 ((c • L) x) := by
      intro r hr x hx
      simp only [LinearMap.smul_apply, map_smul, h r hr x hx]
    have := huniq τ₀ (Ext (c • L) - c • Ext L) (sub_mem (hExtC _ hc) (Submodule.smul_mem _ c (hExtC _ h)))
      (by
        intro x hx
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, hExtA _ hc x hx, hExtA _ h x hx, sub_self]) b hb
    simp only [LinearMap.sub_apply, LinearMap.smul_apply] at this
    rw [sub_eq_zero] at this
    exact this
  have hPupd : ∀ (v : ∀ τ, H τ) (i : ι) (z : H i),
      (fun τ => R τ (update v i z τ)) = update (fun τ => R τ (v τ)) i (R i z) := by
    intro v i z
    funext j
    exact apply_update (fun k => (R k : H k → H k)) v i z j
  have hmemU : ∀ (v : ∀ τ, H τ) (i : ι) (z : H i) τ', update (fun τ => R τ (v τ)) i (R i z) τ' ∈ D' τ' := by
    intro v i z τ'
    rw [← hPupd]
    exact hRmem _ _
  let f : (∀ τ, H τ) → E := fun v => Ext (T.toLinearMap (fun τ => R τ (v τ)) τ₀) (R τ₀ (v τ₀))
  have h0position : ∀ (v : ∀ τ, H τ) (x : H τ₀),
      f (update v τ₀ x) = Ext (T.toLinearMap (fun τ => R τ (v τ)) τ₀) (R τ₀ x) := by
    intro v x
    show Ext (T.toLinearMap (fun τ => R τ (update v τ₀ x τ)) τ₀) (R τ₀ (update v τ₀ x τ₀)) = _
    rw [update_self, toLinearMap_congr T (w := fun τ => R τ (update v τ₀ x τ)) (w' := fun τ => R τ (v τ)) τ₀
      (fun j hj => by simp only [update_of_ne hj])]
  have hiposition : ∀ i, i ≠ τ₀ → ∀ (v : ∀ τ, H τ) (z : H i),
      f (update v i z) = Ext (T.toLinearMap (update (fun τ => R τ (v τ)) i (R i z)) τ₀) (R τ₀ (v τ₀)) := by
    intro i hi v z
    show Ext (T.toLinearMap (fun τ => R τ (update v i z τ)) τ₀) (R τ₀ (update v i z τ₀)) = _
    rw [hPupd, update_of_ne (Ne.symm hi)]
  have hRB : ∀ x, R τ₀ x ∈ B τ₀ := fun x => hD'B _ (hRmem τ₀ x)
  have hgU : ∀ (v : ∀ τ, H τ) (i : ι) (z : H i), ∀ r ∈ Rk τ₀, ∀ x ∈ A τ₀,
      T.toLinearMap (update (fun τ => R τ (v τ)) i (R i z)) τ₀ (r.1 x) =
        r.2 (T.toLinearMap (update (fun τ => R τ (v τ)) i (R i z)) τ₀ x) :=
    fun v i z => goodL _ (fun τ' _ => hmemU v i z τ')
  let T' : MultilinearMap ℂ H E := MultilinearMap.mk' f
    (by
      intro v i x y
      by_cases hi : i = τ₀
      · subst hi
        rw [h0position, h0position, h0position, map_add, map_add]
      · rw [hiposition i hi, hiposition i hi, hiposition i hi, map_add, toLinearMap_update_add T hi,
          ExtAdd _ _ (hgU v i x) (hgU v i y) _ (hRB _)])
    (by
      intro v i c x
      by_cases hi : i = τ₀
      · subst hi
        rw [h0position, h0position, map_smul, map_smul]
      · rw [hiposition i hi, hiposition i hi, map_smul, toLinearMap_update_smul T hi,
          ExtSmul _ _ (hgU v i x) _ (hRB _)])
  have hT'apply : ∀ v, T' v = f v := fun v => rfl
  have goodval : ∀ v : ∀ τ, H τ, (∀ τ', τ' ≠ τ₀ → v τ' ∈ D' τ') →
      T' v = Ext (T.toLinearMap v τ₀) (R τ₀ (v τ₀)) := by
    intro v hv
    rw [hT'apply]
    show Ext (T.toLinearMap (fun τ => R τ (v τ)) τ₀) (R τ₀ (v τ₀)) = _
    rw [toLinearMap_congr T (w := fun τ => R τ (v τ)) (w' := v) τ₀ (fun j hj => hRid j _ (hv j hj))]
  have hgen : ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ D' τ') → ∀ y ∈ D' τ, ∀ τ',
      update u τ y τ' ∈ D' τ' := by
    intro τ u hu y hy τ'
    by_cases h : τ' = τ
    · subst h; rw [update_self]; exact hy
    · rw [update_of_ne h]; exact hu τ' h
  have hshift : ∀ τ (u : ∀ τ, H τ), (∀ τ', τ' ≠ τ → u τ' ∈ D' τ') → ∀ a ∈ A τ₀, ∀ τ', τ' ≠ τ →
      update u τ₀ a τ' ∈ piecewiseSubmodule A B s τ' := by
    intro τ u hu a ha τ' h
    by_cases h' : τ' = τ₀
    · subst h'; rw [update_self, hD0]; exact ha
    · rw [update_of_ne h', ← hD'ne τ' h']; exact hu τ' h
  have hposition0 : ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ₀ → u τ' ∈ D' τ') →
      T'.toLinearMap u τ₀ ∈ C τ₀ ∧
        ∀ r ∈ Rg τ₀, ∀ x ∈ B τ₀, T' (update u τ₀ (r.1 x)) = r.2 (T' (update u τ₀ x)) := by
    intro u hu
    have hL := goodL u hu
    have key : ∀ x, T' (update u τ₀ x) = Ext (T.toLinearMap u τ₀) (R τ₀ x) := by
      intro x
      rw [goodval _ (fun τ' h => by rw [update_of_ne h]; exact hu τ' h), update_self,
        toLinearMap_congr T (w := update u τ₀ x) (w' := u) τ₀ (fun j hj => update_of_ne hj _ _)]
    constructor
    · refine hC τ₀ _ (hExtC _ hL) _ ?_
      intro x hx
      rw [MultilinearMap.toLinearMap_apply, key, hRid _ _ (hBD' _ hx)]
    · intro r hr x hx
      rw [key, key, hRid _ _ (hBD' _ (hRg τ₀ r hr x hx)), hRid _ _ (hBD' _ hx), hExtG _ hL r hr x hx]
  have hpositionEq : ∀ τ, τ ≠ τ₀ → ∀ u : ∀ τ, H τ, (∀ τ', τ' ≠ τ → u τ' ∈ D' τ') →
      ∀ r, r ∈ Rk τ ∪ Rg τ → ∀ y₁ y₂, y₁ ∈ D' τ → y₂ ∈ D' τ →
      (∀ a ∈ A τ₀, T (update (update u τ₀ a) τ y₁) = r.2 (T (update (update u τ₀ a) τ y₂))) →
      T' (update u τ y₁) = r.2 (T' (update u τ y₂)) := by
    intro τ hτ u hu r hr y₁ y₂ hy₁ hy₂ hA
    have hu0 : u τ₀ ∈ D' τ₀ := hu τ₀ (Ne.symm hτ)
    have hg₁ := goodL _ (fun τ' _ => hgen τ u hu y₁ hy₁ τ')
    have hg₂ := goodL _ (fun τ' _ => hgen τ u hu y₂ hy₂ τ')
    rw [goodval _ (fun τ' _ => hgen τ u hu y₁ hy₁ τ'), goodval _ (fun τ' _ => hgen τ u hu y₂ hy₂ τ')]
    simp only [update_of_ne (Ne.symm hτ)]
    rw [hRid _ _ hu0]
    have := huniq τ₀ (Ext (T.toLinearMap (update u τ y₁) τ₀) - r.2 ∘ₗ Ext (T.toLinearMap (update u τ y₂) τ₀))
      (sub_mem (hExtC _ hg₁) (hpostC τ τ₀ hτ r hr _ (hExtC _ hg₂)))
      (by
        intro a ha
        rw [LinearMap.sub_apply, LinearMap.comp_apply, hExtA _ hg₁ a ha, hExtA _ hg₂ a ha,
          MultilinearMap.toLinearMap_apply, MultilinearMap.toLinearMap_apply, update_comm hτ,
          update_comm hτ, hA a ha, sub_self]) (u τ₀) (hD'B _ hu0)
    rwa [LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero] at this
  refine ⟨T', ?_, ?_, ?_⟩
  · intro u hu
    have hL := goodL u (fun τ' _ => hAD' τ' _ (hu τ'))
    rw [goodval u (fun τ' _ => hAD' τ' _ (hu τ')), hRid τ₀ _ (hAD' τ₀ _ (hu τ₀)), hExtA _ hL _ (hu τ₀),
      MultilinearMap.toLinearMap_apply, update_eq_self, hTa u hu]
  · intro τ hτ u hu r hr x hx
    have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
    have hτs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
    exact hpositionEq τ hne u hu r (Set.mem_union_left _ hr) _ _ (hAD' _ _ (hRk τ r hr x hx)) (hAD' _ _ hx)
      (fun a ha => hTb τ hτs (update u τ₀ a) (hshift τ u hu a ha) r hr x hx)
  · intro τ hτ u hu
    by_cases hne : τ = τ₀
    · subst hne
      exact hposition0 u hu
    have hτs : τ ∈ s := by
      rcases Finset.mem_insert.1 hτ with h | h
      · exact absurd h hne
      · exact h
    have hBDτ : ∀ x ∈ B τ, x ∈ D' τ := fun x hx => by
      rw [hD'ne τ hne]; simp only [piecewiseSubmodule, if_pos hτs]; exact hx
    constructor
    · let F : H τ →ₗ[ℂ] H τ₀ →ₗ[ℂ] E := LinearMap.mk₂ ℂ (fun w b => T' (update (update u τ w) τ₀ b))
        (by intro w₁ w₂ b; rw [update_comm hne, update_comm hne, update_comm hne, T'.map_update_add])
        (by intro c w b; rw [update_comm hne, update_comm hne, T'.map_update_smul])
        (by intro w b₁ b₂; rw [T'.map_update_add])
        (by intro c w b; rw [T'.map_update_smul])
      have hF1 : ∀ w ∈ B τ, F w ∈ C τ₀ := by
        intro w hw
        have h := (hposition0 (update u τ w) (fun τ' _ => hgen τ u hu w (hBDτ w hw) τ')).1
        convert h using 1
        ext b
        simp only [F, LinearMap.mk₂_apply, MultilinearMap.toLinearMap_apply]
      have hF2 : ∀ a ∈ A τ₀, F.flip a ∈ C τ := by
        intro a ha
        refine hC τ _ (hTc τ hτs (update u τ₀ a) (hshift τ u hu a ha)).1 _ ?_
        intro x hx
        have hw : ∀ τ', τ' ≠ τ₀ → update (update u τ x) τ₀ a τ' ∈ D' τ' := fun τ' h => by
          rw [update_of_ne h]; exact hgen τ u hu x (hBDτ x hx) τ'
        rw [LinearMap.flip_apply, LinearMap.mk₂_apply, MultilinearMap.toLinearMap_apply, goodval _ hw,
          update_self, hRid _ _ (hAD' _ _ ha), hExtA _ (goodL _ hw) a ha, MultilinearMap.toLinearMap_apply,
          update_idem, update_comm hne]
      have hF3 := hbs τ τ₀ hne F hF1 hF2 (u τ₀) (hD'B _ (hu τ₀ (Ne.symm hne)))
      convert hF3 using 1
      ext x
      rw [LinearMap.flip_apply, LinearMap.mk₂_apply, MultilinearMap.toLinearMap_apply]
      congr 1
      rw [eq_comm, update_eq_self_iff]
      exact (update_of_ne (Ne.symm hne) _ _).symm
    · intro r hr x hx
      exact hpositionEq τ hne u hu r (Set.mem_union_right _ hr) _ _ (hBDτ _ (hRg τ r hr x hx)) (hBDτ _ hx)
        (fun a ha => (hTc τ hτs (update u τ₀ a) (hshift τ u hu a ha)).2 r hr x hx)
end GlobalTheory.FactorwiseExtension
