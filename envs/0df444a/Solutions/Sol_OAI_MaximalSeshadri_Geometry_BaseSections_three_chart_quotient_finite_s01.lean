-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.BaseSections.three_chart_quotient_finite_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:05.531915+00:00
-- url     : https://prove2.me/submissions/5eaaeb43-665b-4b97-a434-2bcce1a487a9

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES002

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentPlane
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section

variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (Ring K) M] [IsScalarTower K (Ring K) M]

theorem quotient_finite [Module.Finite (Ring K) M]
    (A B C : Submodule K M)
    (hA : ∀ z : ℤ × ℤ, 0 ≤ z.2 → ∀ x ∈ A, T (K := K) z • x ∈ A)
    (hB : ∀ z : ℤ × ℤ, 0 ≤ z.1 → ∀ x ∈ B, T (K := K) z • x ∈ B)
    (hC : ∀ z : ℤ × ℤ, z.1 + z.2 ≤ 0 → ∀ x ∈ C, T (K := K) z • x ∈ C)
    (locA : ∀ x : M, ∃ n : ℕ, T (K := K) (0,(n : ℤ)) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, T (K := K) ((n : ℤ),0) • x ∈ B)
    (locC : ∀ x : M, ∃ n : ℕ, T (K := K) (0,-(n : ℤ)) • x ∈ C) :
    Module.Finite K (M ⧸ ((A ⊔ B) ⊔ C)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := Ring K) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  choose c hc using fun i : Fin n => locC (s i)
  let Q := (A ⊔ B) ⊔ C
  let q := Q.mkQ
  let J := (i : Fin n) ×
    (↥(Finset.Icc (-(c i : ℤ) - a i) (b i : ℤ)) ×
     ↥(Finset.Icc (-(c i : ℤ) - b i) (a i : ℤ)))
  let g : J → M ⧸ Q := fun v => q (T (K := K) (v.2.1.val, v.2.2.val) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ × ℤ) : q (T (K := K) z • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z.2
    · have he : z = (z.1, z.2 - a i) + (0, (a i : ℤ)) := by ext <;> simp
      have hm : T (K := K) z • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact hA _ (by dsimp; omega) _ (ha i)
      have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
        ((show A ≤ Q from le_sup_of_le_left le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : (b i : ℤ) ≤ z.1
      · have he : z = (z.1 - b i, z.2) + ((b i : ℤ), 0) := by ext <;> simp
        have hm : T (K := K) z • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact hB _ (by dsimp; omega) _ (hb i)
        have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
          ((show B ≤ Q from le_sup_of_le_left le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · by_cases hzC : z.1 + z.2 ≤ -(c i : ℤ)
        · have he : z = (z.1, z.2 + c i) + (0, -(c i : ℤ)) := by ext <;> simp
          have hm : T (K := K) z • s i ∈ C := by
            rw [he, T_add, mul_smul]
            exact hC _ (by dsimp; omega) _ (hc i)
          have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
            ((show C ≤ Q from le_sup_right) hm)
          rw [hq]; exact W.zero_mem
        · exact Submodule.subset_span
            ⟨⟨i, ⟨⟨z.1, Finset.mem_Icc.mpr (by omega)⟩,
                   ⟨z.2, Finset.mem_Icc.mpr (by omega)⟩⟩⟩, rfl⟩
  have scalar_monomial (i : Fin n) (p : Ring K) : q (p • s i) ∈ W := by
    induction p using AddMonoidAlgebra.induction_on with
    | of z => exact monomial i z
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | smul d p hp =>
      rw [smul_assoc, map_smul]
      exact W.smul_mem d hp
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m, rfl⟩ := Q.mkQ_surjective x
    have hm : m ∈ Submodule.span (Ring K) (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : Ring K, q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro p; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneChartAlgebra
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section
variable {K A R : Type*} [CommRing K] [CommRing A] [CommRing R]

lemma map_unit_zpow (f : A →+* R) (a : Aˣ) (n : ℤ) :
    f (a ^ n : Aˣ) = ((Units.map f a) ^ n : Rˣ) := by
  change (((Units.map f.toMonoidHom) (a ^ n) : Rˣ) : R) = _
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) a n)

lemma lift_cone_left (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u) (hy : f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.2) :
    f (↑(x ^ z.1) * y ^ z.2.toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.2 = (z.2.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_right (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : A) (y : Aˣ) (hx : f x = u) (hy : Units.map f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.1) :
    f (x ^ z.1.toNat * ↑(y ^ z.2)) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.1 = (z.1.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_top (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u * v⁻¹) (hy : f y = ↑(v⁻¹))
    (z : ℤ × ℤ) (hz : z.1 + z.2 ≤ 0) :
    f (↑(x ^ z.1) * y ^ (-(z.1 + z.2)).toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T]
  have hn : ((-(z.1 + z.2)).toNat : ℤ) = -(z.1 + z.2) :=
    Int.toNat_of_nonneg (by omega)
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, hn, ← Units.val_mul]
  congr 1
  rw [mul_zpow, mul_assoc, ← zpow_add]
  have he : z.1 + -(z.1 + z.2) = -z.2 := by omega
  rw [he]
  simp

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineLocalizing
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    have := hf
    have := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_RestrictionLocalization
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

theorem openImmersionTop_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    IsLocalizedModule.Away t (openImmersionTop M f) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have he : X.basicOpen t = f ''ᵁ (⊤ : Y.Opens) :=
    hf.symm.trans (Scheme.Hom.image_top_eq_opensRange f).symm
  let e := (openSectionsCongr M he).trans (restrictedOpenSections M f ⊤).symm
  let g := openRestriction M (X.basicOpen_le t)
  have : IsLocalizedModule.Away t g := affine_openRestriction_localize M t
  have h := IsLocalizedModule.of_linearEquiv (.powers t) g e
  have hp : e.toLinearMap ∘ₗ g = openImmersionTop M f := by
    ext m
    change (restrictedOpenSections M f ⊤).symm
      (openSectionsCongr M he (openRestriction M (X.basicOpen_le t) m)) = _
    rw [openSectionsCongr_restriction]
    rfl
  rwa [hp] at h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ChartModuleMap
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PlaneModules
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

theorem laurentTower (k : K →+* Γ(Y,⊤)) (u v : Γ(Y,⊤)ˣ) (N : Y.Modules) :
    letI := laurentModule k u v N
    IsScalarTower K (LaurentPlane.Ring K) (Sections k N ⊤) := by
  let := laurentModule k u v N
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change LaurentPlane.eval k u v (algebraMap K (LaurentPlane.Ring K) r) •
    (m : OpenSections N ⊤) = k r • (m : OpenSections N ⊤)
  rw [LaurentPlane.eval_algebraMap]

theorem chartMap_clearing [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (a : Γ(X,⊤)) (ha : f.opensRange = X.basicOpen a) (m : Sections kY N ⊤) :
    ∃ d : ℕ, f.appTop a ^ d • m ∈ (chartMap kX kY f hk M e).range := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let F := chartModuleMap M f e
  let : IsLocalizedModule.Away a F := chartModuleMap_localize M f e a ha
  obtain ⟨d,n,hn⟩ := (inferInstance : IsLocalizedModule.Away a F).surj _ _ m
  refine ⟨d,n,?_⟩
  change f.appTop (a^d) • (m : OpenSections N ⊤) = F n at hn
  change F n = f.appTop a ^ d • (m : OpenSections N ⊤)
  rw [map_pow] at hn
  exact hn.symm

lemma chartMap_monomial_mem
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (u v : Γ(Y,⊤)ˣ) (z : ℤ × ℤ)
    (h : ∃ a : Γ(X,⊤), f.appTop a = LaurentPlane.eval kY u v (T z)) :
    letI := laurentModule kY u v N
    ∀ m ∈ (chartMap kX kY f hk M e).range,
      T (K := K) z • m ∈ (chartMap kX kY f hk M e).range := by
  let := laurentModule kY u v N
  rintro m ⟨n,rfl⟩
  obtain ⟨a,ha⟩ := h
  refine ⟨a • n,?_⟩
  change chartMap kX kY f hk M e (a • n) =
    LaurentPlane.eval kY u v (T z) • chartMap kX kY f hk M e n
  rw [chartMap_smul,ha]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneCechFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [Field K] {A B C W : Scheme.{0}}

theorem three_chart_quotient_finite_s01_oai [IsAffine A] [IsAffine B] [IsAffine C]
    (kA : K →+* Γ(A,⊤)) (kB : K →+* Γ(B,⊤))
    (kC : K →+* Γ(C,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ A) (b : W ⟶ B) (c : W ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (hka : a.appTop.hom.comp kA = kW) (hkb : b.appTop.hom.comp kB = kW)
    (hkc : c.appTop.hom.comp kC = kW)
    (LA : LineBundle A) (LB : LineBundle B) (LC : LineBundle C) (N : W.Modules)
    (ea : LA.sheaf.restrict a ≅ N) (eb : LB.sheaf.restrict b ≅ N)
    (ec : LC.sheaf.restrict c ≅ N)
    (u v : Γ(W,⊤)ˣ)
    (ax : Γ(A,⊤)ˣ) (ay : Γ(A,⊤)) (bx : Γ(B,⊤)) (by' : Γ(B,⊤)ˣ)
    (cx : Γ(C,⊤)ˣ) (cy : Γ(C,⊤))
    (hax : Units.map a.appTop.hom ax = u) (hay : a.appTop ay = v)
    (hbx : b.appTop bx = u) (hby : Units.map b.appTop.hom by' = v)
    (hcx : Units.map c.appTop.hom cx = u*v⁻¹) (hcy : c.appTop cy = ↑(v⁻¹))
    (ha : a.opensRange = A.basicOpen ay) (hb : b.opensRange = B.basicOpen bx)
    (hc : c.opensRange = C.basicOpen cy)
    (hfin : letI := laurentModule kW u v N
      Module.Finite (LaurentPlane.Ring K) (Sections kW N ⊤)) :
    Module.Finite K (Sections kW N ⊤ ⧸
      (((chartMap kA kW a hka LA.sheaf ea).range ⊔
        (chartMap kB kW b hkb LB.sheaf eb).range) ⊔
        (chartMap kC kW c hkc LC.sheaf ec).range)) := by
  let := laurentModule kW u v N
  let := laurentTower kW u v N
  let := hfin
  apply LaurentPlane.quotient_finite
  · intro z hz
    apply chartMap_monomial_mem kA kW a hka LA.sheaf ea u v z
    exact ⟨_,LaurentPlane.lift_cone_left kW u v a.appTop.hom ax ay hax hay z hz⟩
  · intro z hz
    apply chartMap_monomial_mem kB kW b hkb LB.sheaf eb u v z
    exact ⟨_,LaurentPlane.lift_cone_right kW u v b.appTop.hom bx by' hbx hby z hz⟩
  · intro z hz
    apply chartMap_monomial_mem kC kW c hkc LC.sheaf ec u v z
    exact ⟨_,LaurentPlane.lift_cone_top kW u v c.appTop.hom cx cy hcx hcy z hz⟩
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kA kW a hka LA.sheaf ea ay ha m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T (0,(n : ℤ))) • m ∈ _
    simpa only [eval_T, zpow_zero, one_mul, zpow_natCast, Units.val_pow_eq_pow_val, hay] using hn
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kB kW b hkb LB.sheaf eb bx hb m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T ((n : ℤ),0)) • m ∈ _
    simpa only [eval_T, zpow_zero, mul_one, zpow_natCast, Units.val_pow_eq_pow_val, hbx] using hn
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kC kW c hkc LC.sheaf ec cy hc m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T (0,-(n : ℤ))) • m ∈ _
    rw [eval_T]
    simp only [zpow_zero, one_mul, zpow_neg, zpow_natCast]
    rw [← inv_pow, Units.val_pow_eq_pow_val]
    simpa only [hcy] using hn

end
end MaximalSeshadri.Geometry.BaseSections

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.BaseSections.three_chart_quotient_finite_s01_oai := @OAI.MaximalSeshadri.Geometry.BaseSections.three_chart_quotient_finite_s01_oai
