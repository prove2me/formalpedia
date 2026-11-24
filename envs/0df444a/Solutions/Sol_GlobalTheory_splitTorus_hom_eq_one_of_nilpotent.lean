-- Prove2me | solution 1 for GlobalTheory.splitTorus_hom_eq_one_of_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:55.744911+00:00
-- url     : https://prove2.me/submissions/b3ce4022-e2a3-4d81-b9cf-43bc9fc210f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_spm_comp
import Theorems.Thm_GlobalTheory_TorusNil_pt_injective
import Theorems.Thm_GlobalTheory_TorusNil_pt_one
import Theorems.Thm_GlobalTheory_TorusNil_exists_pt
import Theorems.Thm_GlobalTheory_TorusNil_mul_pt
import Theorems.Thm_GlobalTheory_TorusNil_comp_eq_of_pullback_map_eq
import Theorems.Thm_GlobalTheory_TorusNil_isIso_torusPt_of
import Theorems.Thm_GlobalTheory_TorusNil_torus_diag
import Theorems.Thm_GlobalTheory_TorusNil_exists_retraction
import Theorems.Thm_GlobalTheory_TorusNil_exists_chart
import Theorems.Thm_GlobalTheory_TorusNil_isNilpotent_of_mem_map
import Theorems.Thm_GlobalTheory_TorusNil_map_mem_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open TorusNil
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A)
    (hJ : IsNilpotent J) (X : Type) [AddCommGroup X] (B : Over (Spec (CommRingCat.of A)))
    [GrpObj B] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f)
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map
        (toUnit _ ≫ η[B])) : f = toUnit _ ≫ η[B] := by
  obtain ⟨R, _, _, j, _, ε, hε⟩ := exists_chart B
  set t := torusPt A X (AddMonoidAlgebra.of A X) with ht
  let K₀ : Ideal (AddMonoidAlgebra A X) := (J ^ (0 + 1)).map (algebraMap A _)
  have h0 : spm (Ideal.Quotient.mkₐ A K₀) ≫ t ≫ f = 1 := by
    rw [← Category.assoc, comp_eq_of_pullback_map_eq h _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J
        (algebraMap A (AddMonoidAlgebra A X ⧸ K₀)) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ (by simpa using ha)))))
      (by rw [← Spec.map_comp]; rfl)]
    exact MonObj.comp_one _
  obtain ⟨φ, hφ⟩ := exists_pt j ε hε (Ideal.Quotient.mkₐ A K₀) Ideal.Quotient.mk_surjective
    (fun x hx => isNilpotent_of_mem_map hJ 0 x (Ideal.Quotient.eq_zero_iff_mem.1 hx)) _ h0
  have main : ∀ k : ℕ, ∀ a, φ a - algebraMap A _ (ε a) ∈
      (J ^ (k + 1)).map (algebraMap A (AddMonoidAlgebra A X)) := by
    intro k
    induction k with
    | zero =>
      intro a
      rw [← hφ, ← pt_one j ε hε, ← Category.assoc, ← spm_comp] at h0
      have := AlgHom.congr_fun (pt_injective j h0) a
      exact Ideal.Quotient.eq.1 this
    | succ k ih =>
      intro a
      have hd : ∀ (g : X →+ X × X) a, (dm A X g).comp φ a - algebraMap A _ (ε a) =
          dm A X g (φ a - algebraMap A _ (ε a)) := by
        intro g a
        rw [map_sub, AlgHom.commutes, AlgHom.comp_apply]
      have hm := mul_pt j ε hε ((J ^ (k + 1)).map (algebraMap A (AddMonoidAlgebra A (X × X))))
        (isNilpotent_of_mem_map hJ k) ((dm A X (AddMonoidHom.inl X X)).comp φ)
        ((dm A X (AddMonoidHom.inr X X)).comp φ)
        ((dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X))).comp φ)
        (fun a => by rw [hd]; exact map_mem_map _ (dm A X _).toLinearMap (ih a))
        (fun a => by rw [hd]; exact map_mem_map _ (dm A X _).toLinearMap (ih a))
        (by
          simp only [spm_comp, Category.assoc, hφ]
          simp only [← Category.assoc]
          rw [← MonObj.mul_comp, ht, torus_diag]) a
      obtain ⟨r, hr⟩ := exists_retraction A X
      rw [← hr (φ a - algebraMap A _ (ε a)), ← hd, ← hd, ← hd]
      apply map_mem_map
      rw [← Ideal.map_pow, ← pow_mul] at hm
      refine Ideal.map_mono (Ideal.pow_le_pow_right (n := (k + 1) * 2) (by omega)) ?_
      convert hm using 1
      ring
  obtain ⟨n, hn⟩ := hJ
  have hφε : φ = (Algebra.ofId A _).comp ε := by
    ext1 a
    have := main n a
    rw [pow_succ, hn] at this
    simpa [sub_eq_zero] using this
  rw [hφε, pt_one j ε hε] at hφ
  haveI := isIso_torusPt_of A X
  have h1 : t ≫ f = t ≫ toUnit _ ≫ η[B] := hφ.symm.trans (MonObj.comp_one t).symm
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]
end GlobalTheory
