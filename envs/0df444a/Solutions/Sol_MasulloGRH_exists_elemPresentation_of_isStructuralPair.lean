-- Prove2me | solution 1 for MasulloGRH.exists_elemPresentation_of_isStructuralPair
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T16:06:07.621033+00:00
-- url     : https://prove2.me/submissions/0f1e4d77-9a03-46c8-9c39-921c875ea64f

import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_compactlyGenerated_exists_elemQuotient
import Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_locallyCompact

set_option autoImplicit false

open Topology Filter Pointwise

namespace MasulloGRHStructAux

theorem eq_one_of_pow_near (w : ℂ) (h : ∀ n : ℕ, ‖w ^ n - 1‖ < 1 / 2) : w = 1 := by
  by_contra hw
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr hw1
  have hre : ∀ n : ℕ, 1 / 2 < (w ^ n).re := fun n => by
    have h1 := h n
    have h2 : |(w ^ n - 1).re| ≤ ‖w ^ n - 1‖ := Complex.abs_re_le_norm _
    have h3 : (w ^ n - 1).re = (w ^ n).re - 1 := by simp
    rw [h3] at h2
    linarith [(abs_le.mp h2).1]
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖w - 1‖)
  have hS : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, w ^ i‖ := by
    calc (N : ℝ) / 2 = ∑ _i ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ ∑ i ∈ Finset.range N, (w ^ i).re := Finset.sum_le_sum fun i _ => (hre i).le
      _ = (∑ i ∈ Finset.range N, w ^ i).re := by rw [Complex.re_sum]
      _ ≤ ‖∑ i ∈ Finset.range N, w ^ i‖ := Complex.re_le_norm _
  rw [geom_sum_eq hw N, norm_div] at hS
  have h4 : ‖w ^ N - 1‖ / ‖w - 1‖ < (1 / 2) / ‖w - 1‖ := div_lt_div_of_pos_right (h N) hpos
  have e : (1 / 2) / ‖w - 1‖ = (1 / ‖w - 1‖) / 2 := by ring
  linarith

theorem sigmaCompact_of_closure_eq_top {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (C : Set H) (hc : IsCompact C) (hg : Subgroup.closure C = ⊤) :
    SigmaCompactSpace H := by
  set T : Set H := C ∪ C⁻¹ ∪ {1} with hT
  have hTc : IsCompact T := (hc.union hc.inv).union isCompact_singleton
  have hTinv : T⁻¹ = T := by
    rw [hT, Set.union_inv, Set.union_inv, inv_inv, Set.inv_singleton, inv_one,
      Set.union_comm C⁻¹ C]
  have hTn : ∀ n : ℕ, IsCompact (T ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact isCompact_singleton
    | succ n ih => rw [pow_succ]; exact ih.mul hTc
  let L : Subgroup H :=
    { carrier := {x | ∃ n : ℕ, x ∈ T ^ n}
      one_mem' := ⟨0, by rw [pow_zero]; exact Set.mem_one.mpr rfl⟩
      mul_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [pow_add]; exact Set.mul_mem_mul ha hb⟩
      inv_mem' := by
        rintro x ⟨a, ha⟩
        refine ⟨a, ?_⟩
        have : x⁻¹ ∈ (T ^ a)⁻¹ := Set.inv_mem_inv.mpr ha
        rwa [← inv_pow, hTinv] at this }
  have hL : Subgroup.closure C ≤ L := by
    rw [Subgroup.closure_le]
    intro x hx
    exact ⟨1, by rw [pow_one]; exact Or.inl (Or.inl hx)⟩
  rw [hg] at hL
  exact ⟨⟨fun n => T ^ n, hTn, Set.iUnion_eq_univ_iff.2 fun x => hL (Subgroup.mem_top x)⟩⟩

end MasulloGRHStructAux

namespace MasulloGRHStructAux

open MasulloGRH in
theorem structure_main {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ k : Subgroup G) (h : IsStructuralPair Γ k) :
    ∃ (m n r s : ℕ) (d : Fin s → ℕ) (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)),
      IsElemPresentation Γ k π := by
  obtain ⟨hΓo, ⟨U₀, hU₀c, hU₀Γ, -, hU₀gen⟩, ⟨hkc, -, A, hA, ⟨C, hCc, hCA, -, hCgen⟩⟩, -⟩ := h
  set N : Subgroup Γ := k.subgroupOf Γ with hN
  have hNc : IsClosed (N : Set Γ) := hkc.preimage continuous_subtype_val
  haveI : LocallyCompactSpace Γ := hΓo.locallyCompactSpace
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hev : Continuous fun p : PontryaginDual G × G => p.1 p.2 :=
    continuous_eval (F := ContinuousMonoidHom G Circle)
  let F : C(Γ × C, ℂ) := ⟨fun p => ((p.2.1 p.1.1 : Circle) : ℂ),
    continuous_subtype_val.comp (hev.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)))⟩
  let Φ₀ : C(Γ, C(C, ℂ)) := F.curry
  have hΦ₀ : ∀ (x : Γ) (χ : C), Φ₀ x χ = ((χ.1 x.1 : Circle) : ℂ) := fun _ _ => rfl
  have hCann : ∀ χ ∈ C, ∀ y ∈ k, χ y = 1 := by
    intro χ hχ y hy
    have : χ ∈ (A : Set (PontryaginDual G)) := hCA hχ
    rw [hA] at this
    exact this y hy
  have hinv : ∀ x y : Γ, x⁻¹ * y ∈ N → Φ₀ x = Φ₀ y := by
    intro x y hxy
    ext χ
    rw [hΦ₀, hΦ₀]
    have h1 : ((y : Γ) : G) = (x : G) * ((x⁻¹ * y : Γ) : G) := by simp
    rw [h1, map_mul, hCann χ.1 χ.2 _ (Subgroup.mem_subgroupOf.mp hxy), mul_one]
  have hsep : ∀ x y : Γ, Φ₀ x = Φ₀ y → x⁻¹ * y ∈ N := by
    intro x y hxy
    rw [Subgroup.mem_subgroupOf]
    by_contra hz
    obtain ⟨χ, hχk, hχz⟩ :=
      pontryaginDual_separates_of_locallyCompact G k hkc ((x⁻¹ * y : Γ) : G) hz
    let S : Subgroup (PontryaginDual G) :=
      { carrier := {ψ | ψ ((x⁻¹ * y : Γ) : G) = 1}
        one_mem' := rfl
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          show a _ * b _ = 1
          rw [ha, hb, mul_one]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at ha ⊢
          show (a ((x⁻¹ * y : Γ) : G))⁻¹ = 1
          rw [ha, inv_one] }
    have hCS : Subgroup.closure C ≤ S := by
      rw [Subgroup.closure_le]
      intro ψ hψ
      show ψ ((x⁻¹ * y : Γ) : G) = 1
      have e1 := congrArg (fun f : C(C, ℂ) => f ⟨ψ, hψ⟩) hxy
      simp only [hΦ₀] at e1
      have e2 : ψ (x : G) = ψ (y : G) := Circle.ext e1
      have h1 : ((x⁻¹ * y : Γ) : G) = (x : G)⁻¹ * (y : G) := by simp
      rw [h1, map_mul, map_inv, e2, inv_mul_cancel]
    have hχA : χ ∈ (A : Set (PontryaginDual G)) := by rw [hA]; exact hχk
    rw [← hCgen] at hχA
    exact hχz (hCS hχA)
  -- descend to the quotient
  let H := Γ ⧸ N
  let Φ : H → C(C, ℂ) := Quotient.lift Φ₀ fun a b hab =>
    hinv a b (QuotientGroup.leftRel_apply.mp hab)
  have hΦc : Continuous Φ := continuous_quot_lift _ Φ₀.continuous
  have hΦmk : ∀ x : Γ, Φ (x : H) = Φ₀ x := fun _ => rfl
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H x =>
    induction b using QuotientGroup.induction_on with | H y =>
    exact QuotientGroup.eq.mpr (hsep x y hab)
  -- compact generation of the quotient
  have hcg : ∃ C' : Set H, IsCompact C' ∧ Subgroup.closure C' = ⊤ := by
    refine ⟨QuotientGroup.mk '' (Subtype.val ⁻¹' U₀ : Set Γ), ?_, ?_⟩
    · refine IsCompact.image ?_ continuous_quot_mk
      rw [Subtype.isCompact_iff, Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hU₀Γ hx⟩, rfl⟩]
      exact hU₀c
    · have h1 : Subgroup.closure (Subtype.val ⁻¹' U₀ : Set Γ) = ⊤ := by
        have := Subgroup.closure_preimage_eq_top U₀
        rw [hU₀gen] at this
        exact this
      show Subgroup.closure ((QuotientGroup.mk' N) '' _) = ⊤
      rw [← MonoidHom.map_closure (QuotientGroup.mk' N), h1,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  -- second countability of the quotient
  have hnhds : (𝓝 (1 : H)).IsCountablyGenerated := by
    obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : H)
    haveI : CompactSpace V := isCompact_iff_compactSpace.mp hVc
    have hemb : IsEmbedding (fun v : V => Φ v.1) :=
      ((hΦc.comp continuous_subtype_val).isClosedEmbedding
        (hΦinj.comp Subtype.val_injective)).isEmbedding
    haveI : TopologicalSpace.MetrizableSpace V := hemb.metrizableSpace
    have e : 𝓝 (1 : H) = map Subtype.val (𝓝 (⟨1, mem_of_mem_nhds hV1⟩ : V)) := by
      rw [map_nhds_subtype_val, nhdsWithin_eq_nhds.mpr hV1]
    rw [e]
    infer_instance
  haveI : SigmaCompactSpace H := sigmaCompact_of_closure_eq_top _ hcg.choose_spec.1
    hcg.choose_spec.2
  haveI hSC : SecondCountableTopology H := by
    letI : UniformSpace H := IsTopologicalGroup.rightUniformSpace H
    haveI : IsUniformGroup H := @isUniformGroup_of_commGroup H _ _ _
    haveI := IsUniformGroup.uniformity_countably_generated (α := H)
    haveI : TopologicalSpace.MetrizableSpace H := UniformSpace.metrizableSpace
    letI := TopologicalSpace.metrizableSpaceMetric H
    exact EMetric.secondCountable_of_sigmaCompact H
  -- apply the structure theorem
  set U : Set H := Φ ⁻¹' Metric.ball (Φ 1) (1 / 2)
  have hU : U ∈ 𝓝 (1 : H) :=
    hΦc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨K', -, hK'U, m, n, r, s, d, π, hd, hπc, hπo, hπs, hπk⟩ :=
    compactlyGenerated_exists_elemQuotient H hcg U hU
  have hK'1 : ∀ q ∈ K', q = 1 := by
    intro q hq
    induction q using QuotientGroup.induction_on with | H x =>
    apply hΦinj
    ext χ
    have hpow : ∀ j : ℕ, ‖(Φ₀ x χ) ^ j - 1‖ < 1 / 2 := fun j => by
      have hm : ((x ^ j : Γ) : H) ∈ U := by
        have := hK'U (K'.pow_mem hq j)
        rwa [← QuotientGroup.mk_pow] at this
      have h1 := (ContinuousMap.dist_apply_le_dist χ).trans_lt (Metric.mem_ball.mp hm)
      rw [dist_eq_norm] at h1
      have e1 : Φ ((x ^ j : Γ) : H) χ = (Φ₀ x χ) ^ j := by
        rw [hΦmk, hΦ₀, hΦ₀]
        simp [map_pow]
      have e2 : Φ (1 : H) χ = 1 := by
        rw [← QuotientGroup.mk_one, hΦmk, hΦ₀]
        simp
      rwa [e1, e2] at h1
    have := eq_one_of_pow_near _ hpow
    rw [hΦmk, this, ← QuotientGroup.mk_one, hΦmk, hΦ₀]
    simp
  refine ⟨m, n, r, s, d, π.comp (QuotientGroup.mk' N), hd, hπc.comp continuous_quot_mk,
    hπo.comp QuotientGroup.isOpenMap_coe, hπs.comp (QuotientGroup.mk'_surjective N), fun x => ?_⟩
  show π (x : H) = 1 ↔ (x : G) ∈ k
  rw [hπk]
  constructor
  · intro hx
    have := hK'1 _ hx
    rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
  · intro hx
    rw [(QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hx)]
    exact K'.one_mem

end MasulloGRHStructAux

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (Γ k : Subgroup G) (h : MasulloGRH.IsStructuralPair Γ k) :
    ∃ (m n r s : ℕ) (d : Fin s → ℕ) (π : ↥Γ →* Multiplicative (MasulloGRH.ElemGroup m n r s d)),
      MasulloGRH.IsElemPresentation Γ k π :=
  MasulloGRHStructAux.structure_main Γ k h

