-- Prove2me | solution 1 for ListHashFurstenberg.Main.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:17:40.554199+00:00
-- url     : https://prove2.me/submissions/fbc179e6-798a-4a01-b385-181d43d1e388

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin
import Theorems.Thm_ListHashFurstenberg_Main_corollary_2_17
import Theorems.Thm_LinMaxLoad_lemma_1

section
set_option autoImplicit false

namespace ListHashFurstenberg.Main.Dev.Cor34

open ListHashFurstenberg.Main
open Classical

/-- `avgLin` computed with any `Fintype` instance on the maps. -/
theorem avgLin_eq {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (r : ℕ) [Fintype (E →ₗ[K] (Fin r → K))] (X : (E →ₗ[K] (Fin r → K)) → ℝ) :
    LinMaxLoad.avgLin K E r X =
      (∑ h, X h) / (Fintype.card (E →ₗ[K] (Fin r → K)) : ℝ) := by
  unfold LinMaxLoad.avgLin
  congr!

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A fixed nonzero vector is killed by a `q^{-k}` fraction of the maps. -/
theorem count_ker (u k : ℕ) [Fintype ((Fin u → F) →ₗ[F] (Fin k → F))] (v : Fin u → F)
    (hv : v ≠ 0) :
    (∑ a : (Fin u → F) →ₗ[F] (Fin k → F), if a v = 0 then (1 : ℝ) else 0) =
      (Fintype.card ((Fin u → F) →ₗ[F] (Fin k → F)) : ℝ) / (Fintype.card F : ℝ) ^ k := by
  have h := (LinMaxLoad.lemma_1 (K := F) (E := Fin u → F) k 1 ![v] ![0]).2
  have hr : Set.range ![v] = {v} := by simp
  rw [hr, finrank_span_singleton hv, mul_one] at h
  unfold LinMaxLoad.probLin at h
  rw [avgLin_eq] at h
  have hc : (0 : ℝ) < Fintype.card ((Fin u → F) →ₗ[F] (Fin k → F)) := by
    exact_mod_cast Fintype.card_pos
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ k := by
    have : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  rw [div_eq_iff hc.ne'] at h
  rw [eq_div_iff hq.ne']
  have h2 : (∑ a : (Fin u → F) →ₗ[F] (Fin k → F), if a v = 0 then (1 : ℝ) else 0) =
      ∑ a : (Fin u → F) →ₗ[F] (Fin k → F), if ∀ i, a (![v] i) = 0 then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    simp
  have h3 : (∑ a : (Fin u → F) →ₗ[F] (Fin k → F), if a v = 0 then (1 : ℝ) else 0) =
      ((Fintype.card F : ℝ) ^ k)⁻¹ * Fintype.card ((Fin u → F) →ₗ[F] (Fin k → F)) := by
    rw [h2, ← h]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  rw [h3]
  field_simp

/-- At least half of the maps to `F^{2t}` are injective on a set of size at most `q^t`. -/
theorem inj_count (u t : ℕ) [Fintype ((Fin u → F) →ₗ[F] (Fin (2 * t) → F))]
    (B0 : Finset (Fin u → F)) (hB : B0.card ≤ Fintype.card F ^ t) :
    (Fintype.card ((Fin u → F) →ₗ[F] (Fin (2 * t) → F)) : ℝ) / 2 ≤
      ∑ a : (Fin u → F) →ₗ[F] (Fin (2 * t) → F),
        if Set.InjOn (⇑a) (↑B0 : Set (Fin u → F)) then (1 : ℝ) else 0 := by
  set cH : ℝ := (Fintype.card ((Fin u → F) →ₗ[F] (Fin (2 * t) → F)) : ℝ) with hcH
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  rw [Finset.sum_boole]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ((Fin u → F) →ₗ[F] (Fin (2 * t) → F))))
    (fun a : (Fin u → F) →ₗ[F] (Fin (2 * t) → F) => Set.InjOn (⇑a) (↑B0 : Set (Fin u → F)))
  rw [Finset.card_univ] at hsplit
  set bad := (Finset.univ : Finset ((Fin u → F) →ₗ[F] (Fin (2 * t) → F))).filter
    (fun a : (Fin u → F) →ₗ[F] (Fin (2 * t) → F) => ¬ Set.InjOn (⇑a) (↑B0 : Set (Fin u → F)))
    with hbaddef
  set piece : Finset (Fin u → F) → Finset ((Fin u → F) →ₗ[F] (Fin (2 * t) → F)) := fun P =>
    (Finset.univ : Finset ((Fin u → F) →ₗ[F] (Fin (2 * t) → F))).filter 
      (fun a => ∀ x ∈ P, ∀ y ∈ P, a x = a y)
  have hsub : bad ⊆ (B0.powersetCard 2).biUnion piece := by
    intro a ha
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Set.InjOn, not_forall,
      Finset.mem_coe] at ha
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := ha
    rw [Finset.mem_biUnion]
    refine ⟨{x, y}, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hne⟩
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · simp only [piece, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rintro z (rfl | rfl) w (rfl | rfl) <;> simp_all
  have hpiece : ∀ P ∈ B0.powersetCard 2, ((piece P).card : ℝ) ≤ cH / q ^ (2 * t) := by
    intro P hP
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2
    have hk := count_ker u (2 * t) (x - y) (sub_ne_zero.mpr hxy)
    rw [Finset.sum_boole] at hk
    rw [← hk]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro a ha
    simp only [piece, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at ha ⊢
    rw [map_sub, sub_eq_zero]
    exact ha x (Or.inl rfl) y (Or.inr rfl)
  have hbad : (bad.card : ℝ) ≤ ((B0.card.choose 2 : ℕ) : ℝ) * (cH / q ^ (2 * t)) := by
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : (bad.card : ℝ) ≤ ∑ P ∈ B0.powersetCard 2, ((piece P).card : ℝ) := by
      exact_mod_cast h1
    refine h2.trans ((Finset.sum_le_sum hpiece).trans ?_)
    rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  have hch : 2 * ((B0.card.choose 2 : ℕ) : ℝ) ≤ q ^ (2 * t) := by
    have hn : 2 * B0.card.choose 2 ≤ (Fintype.card F ^ t) ^ 2 := by
      rw [Nat.choose_two_right]
      calc 2 * (B0.card * (B0.card - 1) / 2) ≤ B0.card * (B0.card - 1) := Nat.mul_div_le _ _
        _ ≤ B0.card * B0.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ Fintype.card F ^ t * Fintype.card F ^ t := Nat.mul_le_mul hB hB
        _ = _ := by ring
    have : (2 * B0.card.choose 2 : ℝ) ≤ ((Fintype.card F ^ t) ^ 2 : ℕ) := by exact_mod_cast hn
    rw [hq, pow_mul', ← Nat.cast_pow, ← Nat.cast_pow]
    rw [pow_two] at this ⊢
    exact_mod_cast this
  have hqp : 0 < q ^ (2 * t) := by positivity
  have hcH0 : 0 ≤ cH := Nat.cast_nonneg _
  have hbad2 : (bad.card : ℝ) ≤ cH / 2 := by
    refine hbad.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ hqp (by norm_num)]
    nlinarith
  have hsplit' : ((Finset.univ.filter (fun a : (Fin u → F) →ₗ[F] (Fin (2 * t) → F) => Set.InjOn (⇑a) (↑B0 : Set (Fin u → F)))).card : ℝ) +
      (bad.card : ℝ) = cH := by
    rw [hcH]; exact_mod_cast hsplit
  linarith

omit [Fintype F] in
/-- A max load of at least `T` gives a bin containing `⌈T⌉₊` points of `S`. -/
theorem exists_bin (u ℓ : ℕ) (b : (Fin u → F) →ₗ[F] (Fin ℓ → F)) (S : Finset (Fin u → F))
    (T : ℝ) (hT : 0 < T) (h : T ≤ (LinMaxLoad.maxLoad b S : ℝ)) :
    ∃ β : Fin ℓ → F, ∃ B0 ⊆ S, B0.card = ⌈T⌉₊ ∧ ∀ s ∈ B0, b s = β := by
  unfold LinMaxLoad.maxLoad at h
  have hne : (S.image b).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    simp at h
    linarith
  obtain ⟨β, -, hβ⟩ := Finset.exists_mem_eq_sup _ hne
    (fun β => (S.filter fun a => b a = β).card)
  rw [hβ] at h
  obtain ⟨B0, hB0, hc⟩ := Finset.exists_subset_card_eq
    (s := S.filter fun a => b a = β) (n := ⌈T⌉₊) (Nat.ceil_le.mpr h)
  exact ⟨β, B0, hB0.trans (Finset.filter_subset _ _), hc,
    fun s hs => (Finset.mem_filter.mp (hB0 hs)).2⟩

omit [Fintype F] in
/-- If `b` is constant on `B0 ⊆ S` and `a` is injective there, the image of `S` under
`e⁻¹ ∘ (a, b)` has `|B0|` points in one coset of `W`. -/
theorem rich_of (u ℓ t N : ℕ) (W : Submodule F (Fin N → F))
    (e : (Fin N → F) ≃ₗ[F] (Fin (2 * t) → F) × (Fin ℓ → F))
    (he : ∀ z, (e z).2 = 0 → z ∈ W)
    (a : (Fin u → F) →ₗ[F] (Fin (2 * t) → F)) (b : (Fin u → F) →ₗ[F] (Fin ℓ → F))
    (S B0 : Finset (Fin u → F)) (β : Fin ℓ → F) (hB0 : B0 ⊆ S) (hβ : ∀ s ∈ B0, b s = β)
    (hinj : Set.InjOn (⇑a) (↑B0 : Set (Fin u → F))) (T : ℝ) (hT : T ≤ B0.card) :
    ∃ x : Fin N → F, T ≤
      (((S.image (e.symm.toLinearMap ∘ₗ a.prod b)).filter fun s => s - x ∈ W).card : ℝ) := by
  set π := e.symm.toLinearMap ∘ₗ a.prod b with hπdef
  have hπ : ∀ s, e (π s) = (a s, b s) := by
    intro s; simp [π]
  refine ⟨e.symm (0, β), hT.trans ?_⟩
  have hinjπ : Set.InjOn (⇑π) (↑B0 : Set (Fin u → F)) := by
    intro x hx y hy hxy
    apply hinj hx hy
    have := congrArg (fun z => (e z).1) hxy
    simpa [hπ] using this
  rw [← Finset.card_image_of_injOn hinjπ]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro y hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_image_of_mem _ (hB0 hs), he _ ?_⟩
  rw [map_sub, hπ, LinearEquiv.apply_symm_apply]
  simp [hβ s hs]

/-- A linear isomorphism `F^N ≅ F^{2t} × F^ℓ` whose second component vanishes only on `W`. -/
theorem exists_equiv (ℓ t : ℕ) (W : Submodule F (Fin (ℓ + 2 * t) → F))
    (hW : Module.finrank F W = 2 * t) :
    ∃ e : (Fin (ℓ + 2 * t) → F) ≃ₗ[F] (Fin (2 * t) → F) × (Fin ℓ → F),
      ∀ z, (e z).2 = 0 → z ∈ W := by
  obtain ⟨W', hc⟩ := W.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun, hW] at h1
  have hW' : Module.finrank F W' = ℓ := by omega
  let eW := LinearEquiv.ofFinrankEq W (Fin (2 * t) → F) (by rw [hW, Module.finrank_fin_fun])
  let eW' := LinearEquiv.ofFinrankEq W' (Fin ℓ → F) (by rw [hW', Module.finrank_fin_fun])
  refine ⟨(Submodule.prodEquivOfIsCompl W W' hc).symm.trans (eW.prodCongr eW'), ?_⟩
  intro z hz
  have h2 : eW' ((Submodule.prodEquivOfIsCompl W W' hc).symm z).2 = 0 := hz
  rw [LinearEquiv.map_eq_zero_iff] at h2
  exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero W W' hc).mp h2

/-- For a fixed `2t`-dimensional `W`, at least a `δ/2` fraction of the maps `π` make `W`
rich for `π(S)`. -/
theorem count_W (u ℓ t : ℕ)
    [Fintype ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F))]
    [Fintype ((Fin u → F) →ₗ[F] (Fin (2 * t) → F))]
    [Fintype ((Fin u → F) →ₗ[F] (Fin ℓ → F))]
    (S : Finset (Fin u → F)) (T : ℝ) (hT : 0 < T) (hTq : ⌈T⌉₊ ≤ Fintype.card F ^ t)
    (W : Submodule F (Fin (ℓ + 2 * t) → F)) (hW : Module.finrank F W = 2 * t) :
    (∑ b : (Fin u → F) →ₗ[F] (Fin ℓ → F),
        if T ≤ (LinMaxLoad.maxLoad b S : ℝ) then (1 : ℝ) else 0) /
        (Fintype.card ((Fin u → F) →ₗ[F] (Fin ℓ → F)) : ℝ) / 2 *
        (Fintype.card ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F)) : ℝ) ≤
      ∑ π : (Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F),
        if ∃ x : Fin (ℓ + 2 * t) → F,
            T ≤ (((S.image π).filter fun s => s - x ∈ W).card : ℝ) then (1 : ℝ) else 0 := by
  obtain ⟨e, he⟩ := exists_equiv ℓ t W hW
  let Ψ : ((Fin u → F) →ₗ[F] (Fin (2 * t) → F)) × ((Fin u → F) →ₗ[F] (Fin ℓ → F)) ≃
      ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F)) :=
    { toFun := fun p => e.symm.toLinearMap ∘ₗ p.1.prod p.2
      invFun := fun π => (LinearMap.fst F _ _ ∘ₗ e.toLinearMap ∘ₗ π,
        LinearMap.snd F _ _ ∘ₗ e.toLinearMap ∘ₗ π)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro π
        ext x
        simp }
  have hcard : (Fintype.card ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F)) : ℝ) =
      (Fintype.card ((Fin u → F) →ₗ[F] (Fin (2 * t) → F)) : ℝ) *
        (Fintype.card ((Fin u → F) →ₗ[F] (Fin ℓ → F)) : ℝ) := by
    rw [← Nat.cast_mul, ← Fintype.card_prod]
    exact_mod_cast (Fintype.card_congr Ψ).symm
  have hℓ0 : (0 : ℝ) < Fintype.card ((Fin u → F) →ₗ[F] (Fin ℓ → F)) := by
    exact_mod_cast Fintype.card_pos
  rw [← Equiv.sum_comp Ψ, Fintype.sum_prod_type, Finset.sum_comm]
  have hper : ∀ b : (Fin u → F) →ₗ[F] (Fin ℓ → F),
      (if T ≤ (LinMaxLoad.maxLoad b S : ℝ) then (1 : ℝ) else 0) *
        ((Fintype.card ((Fin u → F) →ₗ[F] (Fin (2 * t) → F)) : ℝ) / 2) ≤
      ∑ a : (Fin u → F) →ₗ[F] (Fin (2 * t) → F),
        if ∃ x : Fin (ℓ + 2 * t) → F,
            T ≤ (((S.image (Ψ (a, b))).filter fun s => s - x ∈ W).card : ℝ)
          then (1 : ℝ) else 0 := by
    intro b
    by_cases hb : T ≤ (LinMaxLoad.maxLoad b S : ℝ)
    · rw [if_pos hb, one_mul]
      obtain ⟨β, B0, hB0S, hc, hβ⟩ := exists_bin u ℓ b S T hT hb
      refine (inj_count u t B0 (hc ▸ hTq)).trans (Finset.sum_le_sum ?_)
      intro a _
      by_cases ha : Set.InjOn (⇑a) (↑B0 : Set (Fin u → F))
      · rw [if_pos ha, if_pos]
        exact rich_of u ℓ t (ℓ + 2 * t) W e he a b S B0 β hB0S hβ ha T
          (hc ▸ Nat.le_ceil T)
      · rw [if_neg ha]
        split_ifs <;> norm_num
    · rw [if_neg hb, zero_mul]
      exact Finset.sum_nonneg fun a _ => by split_ifs <;> norm_num
  refine le_trans ?_ (Finset.sum_le_sum fun b _ => hper b)
  rw [← Finset.sum_mul, hcard]
  field_simp
  rfl

omit [Fintype F] [DecidableEq F] in
/-- There is a `2t`-dimensional subspace of `F^{ℓ+2t}`. -/
theorem exists_sub (ℓ t : ℕ) :
    ∃ W : Submodule F (Fin (ℓ + 2 * t) → F), Module.finrank F W = 2 * t := by
  let f := LinearMap.funLeft F F (Fin.castAdd (2 * t) : Fin ℓ → Fin (ℓ + 2 * t))
  have hs : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective F F _ (Fin.castAdd_injective _ _)
  refine ⟨LinearMap.ker f, ?_⟩
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h
  omega

/-- Averaging over `W`: some projection `π` makes `π(S)` a `(δ/2)`-Furstenberg set. -/
theorem exists_good_proj (u ℓ t : ℕ)
    [Fintype ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F))]
    [Fintype ((Fin u → F) →ₗ[F] (Fin (2 * t) → F))]
    [Fintype ((Fin u → F) →ₗ[F] (Fin ℓ → F))]
    (S : Finset (Fin u → F)) (T : ℝ) (hT : 0 < T) (hTq : ⌈T⌉₊ ≤ Fintype.card F ^ t) :
    ∃ π : (Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F),
      (∑ b : (Fin u → F) →ₗ[F] (Fin ℓ → F),
        if T ≤ (LinMaxLoad.maxLoad b S : ℝ) then (1 : ℝ) else 0) /
        (Fintype.card ((Fin u → F) →ₗ[F] (Fin ℓ → F)) : ℝ) / 2 ≤
      richFraction (ℓ + 2 * t) (2 * t) T (S.image π) := by
  set δ := (∑ b : (Fin u → F) →ₗ[F] (Fin ℓ → F),
        if T ≤ (LinMaxLoad.maxLoad b S : ℝ) then (1 : ℝ) else 0) /
        (Fintype.card ((Fin u → F) →ₗ[F] (Fin ℓ → F)) : ℝ) / 2 with hδ
  have : Finite (Submodule F (Fin (ℓ + 2 * t) → F)) :=
    Finite.of_injective (fun V : Submodule F (Fin (ℓ + 2 * t) → F) =>
      (V : Set (Fin (ℓ + 2 * t) → F))) SetLike.coe_injective
  let _ : Fintype {W : Submodule F (Fin (ℓ + 2 * t) → F) // Module.finrank F W = 2 * t} :=
    Fintype.ofFinite _
  set R : ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F)) →
      Submodule F (Fin (ℓ + 2 * t) → F) → Prop := fun π V =>
    ∃ x : Fin (ℓ + 2 * t) → F, T ≤ (((S.image π).filter fun s => s - x ∈ V).card : ℝ)
    with hR
  have hrf : ∀ π : (Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F), richFraction (ℓ + 2 * t) (2 * t) T (S.image π) =
      (∑ w : {W : Submodule F (Fin (ℓ + 2 * t) → F) // Module.finrank F W = 2 * t},
        if R π w.1 then (1 : ℝ) else 0) /
      (Fintype.card {W : Submodule F (Fin (ℓ + 2 * t) → F) //
        Module.finrank F W = 2 * t} : ℝ) := by
    intro π
    unfold richFraction
    rw [Nat.card_eq_fintype_card (α := {W : Submodule F (Fin (ℓ + 2 * t) → F) //
        Module.finrank F W = 2 * t})]
    congr 1
    rw [Finset.sum_boole, ← Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun V : Submodule F (Fin (ℓ + 2 * t) → F) => Module.finrank F V = 2 * t)
      (fun V => R π V)), Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨W0, hW0⟩ := exists_sub (F := F) ℓ t
  have hD : (0 : ℝ) < Fintype.card {W : Submodule F (Fin (ℓ + 2 * t) → F) //
      Module.finrank F W = 2 * t} := by
    have hD' : 0 < Fintype.card {W : Submodule F (Fin (ℓ + 2 * t) → F) //
        Module.finrank F W = 2 * t} := Fintype.card_pos_iff.mpr ⟨⟨W0, hW0⟩⟩
    exact_mod_cast hD'
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hlt : ∀ π : (Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F),
      (∑ w : {W : Submodule F (Fin (ℓ + 2 * t) → F) // Module.finrank F W = 2 * t},
        if R π w.1 then (1 : ℝ) else 0) <
      δ * (Fintype.card {W : Submodule F (Fin (ℓ + 2 * t) → F) //
        Module.finrank F W = 2 * t} : ℝ) := by
    intro π
    have := hcon π
    rw [hrf, div_lt_iff₀ hD] at this
    exact this
  have hsum1 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun π _ => hlt π)
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum1
  have hsum2 : ∀ w : {W : Submodule F (Fin (ℓ + 2 * t) → F) // Module.finrank F W = 2 * t},
      δ * (Fintype.card ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F)) : ℝ) ≤
      ∑ π : (Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F), if R π w.1 then (1 : ℝ) else 0 :=
    fun w => count_W u ℓ t S T hT hTq w.1 w.2
  have h3 := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hsum2 w)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
  nlinarith

end ListHashFurstenberg.Main.Dev.Cor34

namespace ListHashFurstenberg.Main

open ListHashFurstenberg.Main.Dev.Cor34 in
theorem chk_corollary_3_4 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (u ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hu : ℓ ≤ u) (T : ℝ) (hT : 8 * (Fintype.card F : ℝ) ≤ T)
    (S : Finset (Fin u → F)) :
    LinMaxLoad.probLin F (Fin u → F) ℓ (fun h => T ≤ (LinMaxLoad.maxLoad h S : ℝ)) ≤
      9 * S.card / ((Fintype.card F : ℝ) ^ ℓ * T) *
        Real.exp (8 * (Fintype.card F : ℝ) *
          (ℓ + 2 * ⌈Real.logb (Fintype.card F) T⌉₊ : ℕ) / T) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set t : ℕ := ⌈Real.logb q T⌉₊ with htdef
  have hq1 : (1 : ℝ) < q := by
    rw [hqdef]; exact_mod_cast Fintype.one_lt_card (α := F)
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T := by linarith
  let _ : Fintype ((Fin u → F) →ₗ[F] (Fin (ℓ + 2 * t) → F)) := Fintype.ofFinite _
  let _ : Fintype ((Fin u → F) →ₗ[F] (Fin (2 * t) → F)) := Fintype.ofFinite _
  let _ : Fintype ((Fin u → F) →ₗ[F] (Fin ℓ → F)) := Fintype.ofFinite _
  have hTq : ⌈T⌉₊ ≤ Fintype.card F ^ t := by
    apply Nat.ceil_le.mpr
    push_cast
    rw [← hqdef]
    calc T = q ^ (Real.logb q T) := (Real.rpow_logb hq0 hq1.ne' hT0).symm
      _ ≤ q ^ (t : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1.le (Nat.le_ceil _)
      _ = q ^ t := Real.rpow_natCast q t
  obtain ⟨π, hπ⟩ := exists_good_proj u ℓ t S T hT0 hTq
  have h17 := corollary_2_17 (ℓ + 2 * t) (2 * t) _ T (S.image π) hπ hT
  have hz : (((ℓ + 2 * t : ℕ) : ℤ) - ((2 * t : ℕ) : ℤ)) = (ℓ : ℤ) := by push_cast; ring
  rw [hz, zpow_natCast] at h17
  have hcardS : ((S.image π).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_image_le
  have hprob : LinMaxLoad.probLin F (Fin u → F) ℓ (fun h => T ≤ (LinMaxLoad.maxLoad h S : ℝ)) =
      (∑ b : (Fin u → F) →ₗ[F] (Fin ℓ → F),
        if T ≤ (LinMaxLoad.maxLoad b S : ℝ) then (1 : ℝ) else 0) /
        (Fintype.card ((Fin u → F) →ₗ[F] (Fin ℓ → F)) : ℝ) := by
    unfold LinMaxLoad.probLin
    rw [avgLin_eq]
  rw [hprob]
  set δ := (∑ b : (Fin u → F) →ₗ[F] (Fin ℓ → F),
        if T ≤ (LinMaxLoad.maxLoad b S : ℝ) then (1 : ℝ) else 0) /
        (Fintype.card ((Fin u → F) →ₗ[F] (Fin ℓ → F)) : ℝ)
  set y : ℝ := 8 * q * ((ℓ + 2 * t : ℕ) : ℝ) / T
  have hneg : -(8 * q * ((ℓ + 2 * t : ℕ) : ℝ)) / T = -y := by rw [neg_div]
  rw [hneg, Real.exp_neg] at h17
  have hey : 0 < Real.exp y := Real.exp_pos y
  have hqℓ : 0 < q ^ ℓ := by positivity
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have key : δ * (q ^ ℓ * T) ≤ 8 * S.card * Real.exp y := by
    have h1 := h17.trans hcardS
    have h2 : δ / 2 * T / 4 * q ^ ℓ * (Real.exp y)⁻¹ * Real.exp y ≤
        S.card * Real.exp y := mul_le_mul_of_nonneg_right h1 hey.le
    rw [mul_assoc _ (Real.exp y)⁻¹, inv_mul_cancel₀ hey.ne', mul_one] at h2
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

end ListHashFurstenberg.Main
end

theorem solution : type_of% @ListHashFurstenberg.Main.chk_corollary_3_4 := @ListHashFurstenberg.Main.chk_corollary_3_4
