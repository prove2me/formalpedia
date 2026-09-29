-- Prove2me | solution 1 for HopfAlgebra.lift_liftPoint_bijective_of_forall_exists_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/731977ae-4589-56e3-8402-03a57827af56

import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq

set_option autoImplicit false
open scoped TensorProduct

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk vanishingIdealOfPoints mem_vanishingIdealOfPoints_iff liftPoint"
p2m_open "HopfAlgebra"
namespace GaloisStablePoints

section Artin

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {S : Type*}

theorem linearIndependent_of_forall_fixed (D : Subgroup (L ≃ₐ[K] L))
    (hD : IntermediateField.fixedField D = ⊥)
    (perm : ∀ σ : L ≃ₐ[K] L, σ ∈ D → S → S)
    (hperm : ∀ σ (hσ : σ ∈ D), Function.Surjective (perm σ hσ))
    {ι : Type*} (v : ι → (S → L))
    (hfix : ∀ (i : ι) (σ : L ≃ₐ[K] L) (hσ : σ ∈ D) (s : S), σ (v i s) = v i (perm σ hσ s))
    (hli : LinearIndependent K v) : LinearIndependent L v := by
  classical
  rw [linearIndependent_iff'] at hli ⊢
  intro t
  induction t using Finset.induction_on with
  | empty => intro g hg i hi; exact absurd hi (Finset.notMem_empty i)
  | @insert a t hat ih =>
    intro g hg

    have hga : g a = 0 := by
      by_contra hne

      set g' : ι → L := fun i => g i / g a with hg'
      have hg'a : g' a = 1 := by simp [hg', hne]
      have hrel' : ∑ i ∈ insert a t, g' i • v i = 0 := by
        have : ∑ i ∈ insert a t, g' i • v i = (g a)⁻¹ • ∑ i ∈ insert a t, g i • v i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hg', smul_smul, div_eq_inv_mul]
        rw [this, hg, smul_zero]

      have hfixg : ∀ (σ : L ≃ₐ[K] L), σ ∈ D → ∀ i ∈ insert a t, σ (g' i) = g' i := by
        intro σ hσ

        have hσrel : ∑ i ∈ insert a t, σ (g' i) • v i = 0 := by
          funext s'
          obtain ⟨s, rfl⟩ := hperm σ hσ s'
          have h0 := congrFun hrel' s
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 ⊢
          have := congrArg σ h0
          rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, hfix i σ hσ s]

        have hdiff : ∑ i ∈ t, (σ (g' i) - g' i) • v i = 0 := by
          have h1 : ∑ i ∈ insert a t, (σ (g' i) - g' i) • v i = 0 := by
            simp only [sub_smul, Finset.sum_sub_distrib, hσrel, hrel', sub_zero]
          rw [Finset.sum_insert hat, hg'a, map_one, sub_self, zero_smul, zero_add] at h1
          exact h1
        have hz := ih (fun i => σ (g' i) - g' i) hdiff
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · rw [hg'a, map_one]
        · exact sub_eq_zero.mp (hz i hi')

      have hK : ∀ i ∈ insert a t, ∃ k : K, algebraMap K L k = g' i := by
        intro i hi
        have hmem : g' i ∈ IntermediateField.fixedField D := by
          rw [IntermediateField.mem_fixedField_iff]
          intro σ hσ
          exact hfixg σ hσ i hi
        rw [hD, IntermediateField.mem_bot] at hmem
        exact hmem
      choose! k hk using hK

      have hKrel : ∑ i ∈ insert a t, k i • v i = 0 := by
        rw [← hrel']
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hk i hi, algebraMap_smul]
      have := hli (insert a t) k hKrel a (Finset.mem_insert_self a t)
      have h1 : g' a = 0 := by rw [← hk a (Finset.mem_insert_self a t), this, map_zero]
      rw [hg'a] at h1
      exact one_ne_zero h1

    have hrel_t : ∑ i ∈ t, g i • v i = 0 := by
      rw [Finset.sum_insert hat, hga, zero_smul, zero_add] at hg
      exact hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hga
    · exact ih g hrel_t i hi'

end Artin

section Main

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {A : Type*} [CommRing A] [Algebra K A]
  {P : Type*} (pt : P → (A →ₐ[K] L)) (S : Set P)

noncomputable def jmap : (A ⧸ vanishingIdealOfPoints (pt '' S)) →ₗ[K] (↥S → L) where
  toFun q s := liftPoint (pt '' S) (pt s.1) (Set.mem_image_of_mem pt s.2) q
  map_add' x y := by funext s; simp only [map_add, Pi.add_apply]
  map_smul' c x := by funext s; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem jmap_mk (a : A) (s : ↥S) : jmap pt S (Ideal.Quotient.mk _ a) s = pt s.1 a := rfl

theorem jmap_injective : Function.Injective (jmap pt S) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [LinearMap.mem_ker] at hq
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [mem_vanishingIdealOfPoints_iff]
  rintro ν ⟨p, hp, rfl⟩
  have := congrFun hq ⟨p, hp⟩
  rwa [jmap_mk] at this

end Main

end GaloisStablePoints
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk vanishingIdealOfPoints mem_vanishingIdealOfPoints_iff liftPoint"
p2m_open "HopfAlgebra"
namespace GaloisStablePoints

section MainB

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {A : Type*} [CommRing A] [Algebra K A]
  {P : Type*} (pt : P → (A →ₐ[K] L)) (S : Set P)

noncomputable def ev : L ⊗[K] A →ₐ[L] (P → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
    (fun _ _ => Commute.all _ _)

noncomputable def evS : L ⊗[K] (A ⧸ vanishingIdealOfPoints (pt '' S)) →ₐ[L] (↥S → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L (↥S → L))
    (Pi.algHom K _ fun s : ↥S => liftPoint (pt '' S) (pt s.1) (Set.mem_image_of_mem pt s.2))
    (fun _ _ => Commute.all _ _)

theorem ev_tmul (c : L) (a : A) (p : P) : ev pt (c ⊗ₜ[K] a) p = c * pt p a := by
  simp only [ev, Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply]
  rw [Algebra.ofId_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem evS_tmul (c : L) (a : A) (s : ↥S) :
    evS pt S (c ⊗ₜ[K] Ideal.Quotient.mk _ a) s = c * pt s.1 a := by
  simp only [evS, Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply]
  rw [Algebra.ofId_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

theorem evS_map_mk (z : L ⊗[K] A) :
    evS pt S (Algebra.TensorProduct.map (AlgHom.id L L)
      (Ideal.Quotient.mkₐ K (vanishingIdealOfPoints (pt '' S))) z) = fun s => ev pt z s.1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul c a =>
    funext s
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, evS_tmul, ev_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    rfl

theorem evS_surjective (hev : Function.Surjective (ev pt)) : Function.Surjective (evS pt S) := by
  classical
  intro g
  let g' : P → L := fun p => if h : p ∈ S then g ⟨p, h⟩ else 0
  obtain ⟨y, hy⟩ := hev g'
  refine ⟨Algebra.TensorProduct.map (AlgHom.id L L) (Ideal.Quotient.mkₐ K _) y, ?_⟩
  rw [evS_map_mk, hy]
  funext s
  simp [g', s.2]

variable [Module.Finite K A] [Finite P]

theorem finrank_quot_le (D : Subgroup (L ≃ₐ[K] L)) (hD : IntermediateField.fixedField D = ⊥)
    (hpt : Function.Injective pt)
    (hstab : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ p ∈ S, ∃ p' ∈ S, ∀ a : A, pt p' a = σ (pt p a)) :
    Module.finrank K (A ⧸ vanishingIdealOfPoints (pt '' S)) ≤ Module.finrank L (↥S → L) := by
  classical

  have hperm : ∀ (σ : L ≃ₐ[K] L) (hσ : σ ∈ D), ∃ f : ↥S → ↥S, Function.Surjective f ∧
      ∀ (s : ↥S) (a : A), pt (f s).1 a = σ (pt s.1 a) := by
    intro σ hσ
    choose f hfS hf using fun s : ↥S => hstab σ hσ s.1 s.2
    let F : ↥S → ↥S := fun s => ⟨f s, hfS s⟩
    have hinj : Function.Injective F := by
      intro s s' h
      apply Subtype.ext
      apply hpt
      apply AlgHom.ext
      intro a
      apply σ.injective
      rw [← hf s a, ← hf s' a]
      exact congrArg (fun u : ↥S => pt u.1 a) h
    exact ⟨F, Finite.surjective_of_injective hinj, fun s a => hf s a⟩
  choose perm hpermS hpermpt using hperm

  let bQ := Module.Free.chooseBasis K (A ⧸ vanishingIdealOfPoints (pt '' S))
  have hliK : LinearIndependent K (fun i => jmap pt S (bQ i)) :=
    bQ.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (jmap_injective pt S))
  have hliL : LinearIndependent L (fun i => jmap pt S (bQ i)) := by
    refine linearIndependent_of_forall_fixed D hD perm hpermS _ ?_ hliK
    intro i σ hσ s
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (bQ i)
    rw [← ha, jmap_mk, jmap_mk, hpermpt]
  have h1 := hliL.fintype_card_le_finrank
  rwa [Module.finrank_eq_card_chooseBasisIndex]

theorem evS_bijective (D : Subgroup (L ≃ₐ[K] L)) (hD : IntermediateField.fixedField D = ⊥)
    (hpt : Function.Injective pt) (hev : Function.Bijective (ev pt))
    (hstab : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ p ∈ S, ∃ p' ∈ S, ∀ a : A, pt p' a = σ (pt p a)) :
    Function.Bijective (evS pt S) := by
  classical
  have hsurj := evS_surjective pt S hev.2
  set Q := A ⧸ vanishingIdealOfPoints (pt '' S)
  have hfr : Module.finrank L (L ⊗[K] Q) = Module.finrank K Q := Module.finrank_baseChange
  have hle : Module.finrank L (L ⊗[K] Q) ≤ Module.finrank L (↥S → L) := by
    rw [hfr]; exact finrank_quot_le pt S D hD hpt hstab
  have hge : Module.finrank L (↥S → L) ≤ Module.finrank L (L ⊗[K] Q) := by
    have hr : LinearMap.range (evS pt S).toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
    calc Module.finrank L (↥S → L) = Module.finrank L (⊤ : Submodule L (↥S → L)) := (finrank_top L _).symm
      _ = Module.finrank L (LinearMap.range (evS pt S).toLinearMap) := by rw [hr]
      _ ≤ Module.finrank L (L ⊗[K] Q) := LinearMap.finrank_range_le _
  have heq : Module.finrank L (L ⊗[K] Q) = Module.finrank L (↥S → L) := le_antisymm hle hge
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hsurj, hsurj⟩

end MainB

end GaloisStablePoints
end HopfAlgebra

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Subgroup (L ≃ₐ[K] L)) (hD : IntermediateField.fixedField D = ⊥)
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    {P : Type*} [Finite P] (pt : P → (A →ₐ[K] L)) (hpt : Function.Injective pt)
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    (S : Set P) (hstab : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ p ∈ S, ∃ p' ∈ S, ∀ a : A, pt p' a = σ (pt p a)) :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (↥S → L))
        (Pi.algHom K _ fun s : ↥S =>
          HopfAlgebra.liftPoint (pt '' S) (pt s.1) (Set.mem_image_of_mem pt s.2))
        (fun _ _ => Commute.all _ _) :
        L ⊗[K] (A ⧸ HopfAlgebra.vanishingIdealOfPoints (pt '' S)) →ₐ[L] (↥S → L)) :=
  HopfAlgebra.GaloisStablePoints.evS_bijective pt S D hD hpt hev hstab

end S_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq
end P2MW
export P2MW.S_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq (solution)
