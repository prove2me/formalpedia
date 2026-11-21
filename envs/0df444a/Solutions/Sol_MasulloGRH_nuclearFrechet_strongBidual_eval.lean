-- Prove2me | solution 1 for MasulloGRH.nuclearFrechet_strongBidual_eval
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:45:47.902488+00:00
-- url     : https://prove2.me/submissions/8354e023-5ff1-403c-ad3f-8c9aadd68e04

import Mathlib
import Theorems.Thm_MasulloGRH_bounded_iff_weakly_bounded
import Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
import Theorems.Thm_MasulloGRH_nuclear_bounded_precompact

open Set Filter Topology Bornology MasulloGRH
open scoped Pointwise

private theorem compact_of_closed_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hc : IsCompleteTVS E) (hN : IsNuclear E)
    {D : Set E} (hD : IsClosed D) (hb : IsVonNBounded ℂ D) : IsCompact D := by
  obtain ⟨⟨ι,_,p,hp⟩,_⟩ := hN.1
  have hadd := hp.topologicalAddGroup
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have hu : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hcomp : CompleteSpace E := by
    refine ⟨fun {f} hf => hc.2 f ⟨hf.1, fun V hV => ?_⟩⟩
    have hmem : {z : E × E | z.2 - z.1 ∈ V} ∈ uniformity E := by
      rw [uniformity_eq_comap_nhds_zero E]
      exact preimage_mem_comap hV
    obtain ⟨A,hA,hsub⟩ := mem_prod_same_iff.mp (hf.2 hmem)
    exact ⟨A,hA,fun x hx y hy => hsub (mk_mem_prod hy hx)⟩
  apply TotallyBounded.isCompact_of_isComplete _ hD.isComplete
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro V hV
  obtain ⟨t,ht⟩ := nuclear_bounded_precompact E hN D hb V hV
  refine ⟨(t:Set E),t.finite_toSet,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion₂.mpr ⟨y,hy,x-y,hxy,by simp [vadd_eq_add]⟩

private theorem weak_sep {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (K : Set (WeakDual ℂ G)) (hv : Convex ℝ K) (hc : IsClosed K) (L : WeakDual ℂ G)
    (h : L ∉ K) : ∃ (g:G) (u:ℝ), (∀ k ∈ K, (k g).re < u) ∧ u < (L g).re := by
  have tower : IsScalarTower ℝ ℂ (WeakDual ℂ G) :=
    ⟨fun a c f => by apply DFunLike.ext; intro x; exact smul_assoc a c (f x)⟩
  have hlcs : LocallyConvexSpace ℝ (WeakDual ℂ G) :=
    (topDualPairing ℂ G).weakBilin_withSeminorms.toLocallyConvexSpace
  obtain ⟨l,u,hK,hL⟩ := @RCLike.geometric_hahn_banach_closed_point ℂ
      (WeakDual ℂ G) _ _ _ K L _ _ tower _ _ hlcs hv hc h
  obtain ⟨g,rfl⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ G) l
  exact ⟨g,u,hK,hL⟩

private theorem complete_nuclear_eval (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hc : IsCompleteTVS E) (hN : IsNuclear E)
    (F : StrongDual ℂ (StrongDual ℂ E)) : ∃ y : E, ∀ f : StrongDual ℂ E, F f = f y := by
  classical
  have hL := hN.1
  obtain ⟨⟨ι,_,p,hp⟩,_⟩ := hL
  have hadd := hp.topologicalAddGroup
  have hsmul := hp.continuousSMul
  let q := F.toLinearMap.toSeminorm
  have hq : Continuous q := F.continuous.norm
  obtain ⟨B,C,hB,hC,hbound⟩ := strongDual_seminorm_le_polar E hN.1 q hq
  let M := max C 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCM : C ≤ M := le_max_left _ _
  let D := {y : E | ∀ (g : StrongDual ℂ E) (r : ℝ), 0 ≤ r →
    (∀ x ∈ B, ‖g x‖ ≤ r) → ‖g y‖ ≤ r}
  have hD : IsClosed D := by
    dsimp [D]
    simp only [ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun r => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_le g.continuous.norm continuous_const
  have hDB : IsVonNBounded ℂ D := by
    apply (bounded_iff_weakly_bounded E hN.1 D).mpr
    intro g
    obtain ⟨r,hr⟩ := isBounded_iff_forall_norm_le.mp ((bounded_iff_weakly_bounded E hN.1 B).mp hB g)
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max r 0, ?_⟩
    rintro _ ⟨y,hy,rfl⟩
    exact hy g _ (le_max_right _ _) (fun x hx => (hr _ ⟨x,hx,rfl⟩).trans (le_max_left _ _))
  have hBD : B ⊆ D := fun x hx g r h hr => hr x hx
  have hd0 : (0:E) ∈ D := fun g r hr _ => by simpa using hr
  let J (y:E) : WeakDual ℂ (StrongDual ℂ E) := StrongDual.toWeakDual
    ({toFun := fun g => g y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      cont := continuous_eval_const y} : StrongDual ℂ (StrongDual ℂ E))
  have hJ (y:E) (g:StrongDual ℂ E) : J y g = g y := rfl
  have hJc : Continuous J := WeakDual.continuous_of_continuous_eval fun g => g.continuous
  let K := J '' D
  have hKc : IsClosed K := ((compact_of_closed_bounded hc hN hD hDB).image hJc).isClosed
  have hKv : Convex ℝ K := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ a b ha hb hab
    refine ⟨(a:ℂ) • x + (b:ℂ) • y,?_,?_⟩
    · intro g r hr hrB
      rw [map_add,map_smul,map_smul]
      calc
        _ ≤ ‖(a:ℂ) • g x‖ + ‖(b:ℂ) • g y‖ := norm_add_le _ _
        _ = a*‖g x‖ + b*‖g y‖ := by simp [abs_of_nonneg ha,abs_of_nonneg hb]
        _ ≤ a*r+b*r := add_le_add (mul_le_mul_of_nonneg_left (hx g r hr hrB) ha) (mul_le_mul_of_nonneg_left (hy g r hr hrB) hb)
        _ = r := by rw [←add_mul,hab,one_mul]
    · apply DFunLike.ext; intro g
      change g ((a:ℂ) • x + (b:ℂ) • y) = a • g x + b • g y
      rw [map_add,map_smul,map_smul]
      rfl
  let L := StrongDual.toWeakDual ((M:ℂ)⁻¹ • F)
  have hLK : L ∈ K := by
    by_contra h
    obtain ⟨g,u,huK,huL⟩ := weak_sep K hKv hKc L h
    have hsep (y:E) (hy:y∈D) : (g y).re < u := huK (J y) ⟨y,hy,rfl⟩
    have hu : 0 < u := by simpa using hsep _ hd0
    have hs (x:E) (hx:x∈B) : ‖g x‖ ≤ u := by
      obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (g x)
      have hDcx : c • x ∈ D := by
        intro f r hr hrB
        rw [map_smul,norm_smul,hc,one_mul]
        exact hrB x hx
      have hh := hsep _ hDcx
      rw [map_smul,smul_eq_mul,← he,Complex.ofReal_re] at hh
      exact hh.le
    have hf : ‖F g‖ ≤ C*u := hbound g u hu.le hs
    have hLg : ‖L g‖ ≤ u := by
      change ‖(M:ℂ)⁻¹ * F g‖ ≤ u
      rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hM.le]
      exact (inv_mul_le_iff₀ hM).mpr (hf.trans (mul_le_mul_of_nonneg_right hCM hu.le))
    exact (huL.trans_le (Complex.re_le_norm _)).not_ge hLg
  obtain ⟨y,_,hy⟩ := hLK
  refine ⟨(M:ℂ) • y,?_⟩
  intro g
  have hg := congrArg (fun H : WeakDual ℂ (StrongDual ℂ E) => H g) hy
  change g y = (M:ℂ)⁻¹ * F g at hg
  rw [map_smul,smul_eq_mul,hg,mul_inv_cancel_left₀ (by exact_mod_cast hM.ne')]

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (F : StrongDual ℂ (StrongDual ℂ E)) : ∃ y : E, ∀ f : StrongDual ℂ E, F f = f y :=
  complete_nuclear_eval E hE.2.1 hN F
