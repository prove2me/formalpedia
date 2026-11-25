-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.tailSum_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:54.658387+00:00
-- url     : https://prove2.me/submissions/549fb6d6-3376-4e26-94fb-ea9523f408d7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_Spherical_tailEmb_injective
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n) (S : Finset (Fin n))
    (hS : S.card = m) : tailSum ν hm ≤ ∑ i ∈ S, ν i := by
  classical
  set T := Finset.univ.image (tailEmb hm)
  have hT : T.card = m := by
    rw [Finset.card_image_of_injective _ (tailEmb_injective hm), Finset.card_univ, Fintype.card_fin]
  have hsumT : tailSum ν hm = ∑ i ∈ T, ν i := by
    rw [Finset.sum_image fun a _ b _ h => tailEmb_injective hm h]
    rfl
  have hmemT : ∀ y ∈ T, n - m ≤ y.val := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    simp [tailEmb]
  have hnotT : ∀ x, x ∉ T → x.val < n - m := by
    intro x hx
    by_contra h
    exact hx (Finset.mem_image.2 ⟨⟨x.val - (n - m), by omega⟩, Finset.mem_univ _,
      Fin.ext (by simp [tailEmb]; omega)⟩)
  have e1 := Finset.sum_sdiff (f := ν) (Finset.inter_subset_left (s₁ := S) (s₂ := T))
  have e2 := Finset.sum_sdiff (f := ν) (Finset.inter_subset_left (s₁ := T) (s₂ := S))
  rw [Finset.sdiff_inter_self_left] at e1 e2
  rw [Finset.inter_comm T S] at e2
  rw [hsumT, ← e1, ← e2]
  suffices key : ∑ i ∈ T \ S, ν i ≤ ∑ i ∈ S \ T, ν i by linarith
  have hcard : (T \ S).card = (S \ T).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm, hS, hT]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have : S = ∅ := Finset.card_eq_zero.1 hS
    have : T = ∅ := Finset.card_eq_zero.1 hT
    simp [*]
  · set c := ν ⟨n - m, by omega⟩
    calc ∑ i ∈ T \ S, ν i ≤ (T \ S).card • c :=
          Finset.sum_le_card_nsmul _ _ _ fun y hy =>
            hν (show (⟨n - m, by omega⟩ : Fin n) ≤ y from hmemT y (Finset.mem_sdiff.1 hy).1)
      _ = (S \ T).card • c := by rw [hcard]
      _ ≤ ∑ i ∈ S \ T, ν i :=
          Finset.card_nsmul_le_sum _ _ _ fun x hx =>
            hν (show x ≤ (⟨n - m, by omega⟩ : Fin n) from
              (Fin.le_def.2 (hnotT x (Finset.mem_sdiff.1 hx).2).le))
end GroundTheory.Automorphic.Spherical
