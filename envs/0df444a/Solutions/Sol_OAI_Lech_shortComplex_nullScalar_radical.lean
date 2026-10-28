-- Prove2me | solution 1 for OAI.Lech.shortComplex_nullScalar_radical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:09:57.390254+00:00
-- url     : https://prove2.me/submissions/91e14cb8-5099-404e-aa6f-03ee7bf68b15

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L006
import Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProjectiveGhost
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
namespace Lech.ProjectiveGhost
universe u
variable {R : Type u} [CommRing R]

lemma scalar_cycle_boundary (S : ShortComplex (ModuleCat.{u} R)) (x : R)
    (hx : ∀ z : S.homology, x • z = 0) (y : S.X₂) (hy : S.g y = 0) :
    ∃ z : S.X₁, S.f z = x • y := by
  let c : LinearMap.ker S.g.hom := ⟨y,hy⟩
  let Q := LinearMap.range S.moduleCatToCycles
  let q : (LinearMap.ker S.g.hom) ⧸ Q := Q.mkQ c
  have hq : x • q = 0 := by
    let e := S.moduleCatHomologyIso.toLinearEquiv
    have h := congrArg e (hx (e.symm q))
    have hz := (e.map_smul x (e.symm q)).symm.trans (h.trans e.map_zero)
    exact (congrArg (fun z => x • z) (e.apply_symm_apply q)).symm.trans hz
  have hc : x • c ∈ Q := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact (map_smul Q.mkQ x c).trans hq
  obtain ⟨z,hz⟩ := hc
  exact ⟨z,congrArg Subtype.val hz⟩

 

lemma correct (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (j : ℤ) [Module.Projective R (F.X j)]
    (hx : ∀ z : F.homology j, x • z = 0)
    (f : F ⟶ F) (hf : ∀ i, j < i → f.f i = 0) :
    ∃ f' : F ⟶ F, Nonempty (Homotopy (x • f) f') ∧
      ∀ i, j ≤ i → f'.f i = 0 := by
  have hcycles (v : F.X j) : (F.d j (j+1)) (f.f j v) = 0 := by
    have h := congrArg (fun g : F.X j ⟶ F.X (j+1) => g v) (f.comm j (j+1))
    rw [hf (j+1) (by omega)] at h
    rw [comp_zero] at h
    exact h
  have hmem (v : F.X j) : x • f.f j v ∈ LinearMap.range (F.d (j-1) j).hom := by
    let e := F.homologyIsoSc' (j-1) j (j+1) (by simp) (by simp)
    have hx' (z : (F.sc' (j-1) j (j+1)).homology) : x • z = 0 := by
      let l := e.toLinearEquiv
      calc
        x • z = l (x • l.symm z) := by rw [l.map_smul,l.apply_symm_apply]
        _ = l 0 := congrArg l (hx (l.symm z))
        _ = 0 := l.map_zero
    obtain ⟨w,hw⟩ := scalar_cycle_boundary (F.sc' (j-1) j (j+1)) x hx'
      (f.f j v) (hcycles v)
    exact ⟨w,hw⟩
  let a : F.X j →ₗ[R] LinearMap.range (F.d (j-1) j).hom :=
    (x • (f.f j).hom).codRestrict _ hmem
  obtain ⟨h,hh⟩ := Module.projective_lifting_property
    (F.d (j-1) j).hom.rangeRestrict a (F.d (j-1) j).hom.surjective_rangeRestrict
  have hh' : ModuleCat.ofHom h ≫ F.d (j-1) j = x • f.f j := by
    apply ModuleCat.hom_ext
    ext v
    exact congrArg Subtype.val (LinearMap.congr_fun hh v)
  let α : Cochain F F (-1) := Cochain.single (ModuleCat.ofHom h) (-1)
  let b : F ⟶ F := (Cocycle.mk (δ (-1) 0 α) 1 (by norm_num) (δ_δ _ _ _ _)).homOf
  have hb : Cochain.ofHom b = δ (-1) 0 α := Cocycle.cochain_ofHom_homOf_eq_coe _
  have hb0 : Homotopy b 0 := (Cochain.equivHomotopy b 0).symm ⟨α, by simpa using hb⟩
  refine ⟨x • f - b, ⟨?_⟩, ?_⟩
  · simpa [sub_eq_add_neg] using ((Homotopy.refl (x • f)).add (hb0.smul (-1:R))).symm
  · intro i hi
    have hbval := Cochain.congr_v hb i i (by omega)
    rw [δ_v (-1) 0 (by norm_num) α i i (by omega) (i-1) (i+1) (by omega) (by omega)] at hbval
    have hz : (Cochain.single (ModuleCat.ofHom h) (-1)).v (i+1) i (by omega) = 0 :=
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)
    by_cases he : i=j
    · subst i
      simp only [α,Cochain.single_v,hz,comp_zero,smul_zero,add_zero,
        Cochain.ofHom_v] at hbval
      simp [hbval,hh']
    · have hz' : (Cochain.single (ModuleCat.ofHom h) (-1)).v i (i-1) (by omega) = 0 :=
        Cochain.single_v_eq_zero _ _ _ _ _ he
      simp only [α,hz,hz',zero_comp,comp_zero,smul_zero,add_zero,
        Cochain.ofHom_v] at hbval
      simp [hf i (by omega),hbval]
 

theorem nullhomotopy_pow (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (m : ℤ) (N : ℕ) (hp : ∀ i, Module.Projective R (F.X i))
    (hb : ∀ i, i < m ∨ m+N ≤ i → IsZero (F.X i))
    (x : R) (hx : ∀ i (z : F.homology i), x • z = 0) :
    Nonempty (Homotopy (x^N • 𝟙 F) 0) := by
  have (i : ℤ) : Module.Projective R (F.X i) := hp i
  have hstep (n : ℕ) : ∃ f : F ⟶ F, Nonempty (Homotopy (x^n • 𝟙 F) f) ∧
      ∀ i, m+N-(n:ℤ) ≤ i → f.f i = 0 := by
    induction n with
    | zero =>
      refine ⟨𝟙 F,⟨by simpa using Homotopy.refl (𝟙 F)⟩,?_⟩
      intro i hi
      exact (hb i (Or.inr (by simpa using hi))).eq_of_src _ _
    | succ n ih =>
      obtain ⟨f,⟨H⟩,hf⟩ := ih
      obtain ⟨f',⟨H'⟩,hf'⟩ := correct F x (m+N-n-1) (hx _) f
        (fun i hi => hf i (by omega))
      refine ⟨f',⟨?_⟩,fun i hi => hf' i (by omega)⟩
      simpa [smul_smul,pow_succ,mul_comm] using (H.smul x).trans H'
  obtain ⟨f,⟨H⟩,hf⟩ := hstep N
  have he : f=0 := by
    ext i : 1
    by_cases hi : i < m
    · exact (hb i (Or.inl hi)).eq_of_src _ _
    · exact hf i (by omega)
  exact ⟨H.trans (Homotopy.ofEq he)⟩
 

theorem exists_nullhomotopy_power [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ)
    (hp : ∀ i, Module.Projective R (F.X i))
    (hb : ∀ i, i < m ∨ m+N ≤ i → IsZero (F.X i))
    (hH : ∀ i, IsFiniteLength R (F.homology i))
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, Nonempty (Homotopy (x^a • 𝟙 F) 0) := by
  classical
  let M := ∀ i : Fin N,F.homology (m+i)
  have (i : Fin N) : IsNoetherian R (F.homology (m+i)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hH _)).1
  have (i : Fin N) : IsArtinian R (F.homology (m+i)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hH _)).2
  have hM : IsFiniteLength R M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance,inferInstance⟩
  obtain ⟨I,hIr,hI⟩ := Lech.finiteLength_primary_annihilator hM
  obtain ⟨a,ha⟩ := Ideal.mem_radical_iff.mp (show x ∈ I.radical from hIr.symm ▸ hx)
  have hkill (i : ℤ) (z : F.homology i) : x^a • z = 0 := by
    by_cases hi : i < m ∨ m+N ≤ i
    · have hz := ExactAt.isZero_homology (ExactAt.of_isZero (hb i hi))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      exact Subsingleton.elim _ _
    · obtain ⟨j,rfl⟩ : ∃ j : Fin N,m+j=i :=
        ⟨⟨(i-m).toNat,by omega⟩,by change m + ((i-m).toNat:ℤ) = i; omega⟩
      have hz := Module.mem_annihilator.mp (hI ha) (Pi.single j z)
      have hz' := congrFun hz j
      change x^a • ((Pi.single j z : M) j) = 0 at hz'
      simpa only [Pi.single_eq_same] using hz' 
  refine ⟨a*N,?_⟩
  simpa only [pow_mul] using nullhomotopy_pow F m N hp hb (x^a) hkill
end Lech.ProjectiveGhost

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma shortComplex_nullScalar_radical_oai [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    IsLocalRing.maximalIdeal R ≤ (Koszul.nullScalarIdeal F).radical := by
  intro x hx
  obtain ⟨a,ha⟩ := ProjectiveGhost.exists_nullhomotopy_power F
    (-(dimension R : ℤ)) (dimension R+1)
    (fun i => by have := hF.term_free i; infer_instance)
    (fun i hi => hF.bounded i (by omega)) hF.homology_finite_length x hx
  exact ⟨a,ha⟩



end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.shortComplex_nullScalar_radical_oai.{u} := @OAI.Lech.shortComplex_nullScalar_radical_oai.{u}
