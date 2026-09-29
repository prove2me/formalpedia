-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.level_indep_and_span_of_isPullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2aca079b-1c59-512c-9d71-29a0f03d49d9

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq
import Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat.GoodReductionJacobian"
open scoped TensorProduct

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.nsmul_succ"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "finComb pointGroup mul_inv_cancel mul_assoc mul_one one mul_natural one_mul mul nsmul nsmul_succ"
namespace LevelDescentAux
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Hom

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {A₁ A₂ T₁ T₂ : Scheme.{u}}
  {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)}
  (L₁ : RelativeGroupLaw R₁ f₁) (L₂ : RelativeGroupLaw R₂ f₂)
  (t₁ : T₁ ⟶ Spec (CommRingCat.of R₁)) (t₂ : T₂ ⟶ Spec (CommRingCat.of R₂))
  (φ : SchemeHomOver t₁ f₁ → SchemeHomOver t₂ f₂)
  (hmul : ∀ x y, φ (L₁.mul t₁ x y) = L₂.mul t₂ (φ x) (φ y))

include hmul

lemma map_one : φ (L₁.one t₁) = L₂.one t₂ := by
  letI := L₂.pointGroup t₂
  have h : φ (L₁.one t₁) * φ (L₁.one t₁) = φ (L₁.one t₁) := by
    change L₂.mul t₂ _ _ = _
    rw [← hmul, L₁.one_mul]
  calc φ (L₁.one t₁) = φ (L₁.one t₁) * φ (L₁.one t₁) * (φ (L₁.one t₁))⁻¹ := by
        rw [_root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
    _ = 1 := by rw [h, _root_.mul_inv_cancel]

lemma map_nsmul (n : ℕ) (x : SchemeHomOver t₁ f₁) : φ (L₁.nsmul t₁ n x) = L₂.nsmul t₂ n (φ x) := by
  induction n with
  | zero => exact map_one L₁ L₂ t₁ t₂ φ hmul
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hmul, ih]

lemma map_finComb {m : ℕ} (x : Fin m → SchemeHomOver t₁ f₁) (e : Fin m → ℕ) :
    φ (L₁.finComb t₁ x e) = L₂.finComb t₂ (fun i => φ (x i)) e := by
  letI i₁ := L₁.pointGroup t₁
  letI i₂ := L₂.pointGroup t₂
  let Φ : SchemeHomOver t₁ f₁ →* SchemeHomOver t₂ f₂ := MonoidHom.mk' φ hmul
  change Φ (List.ofFn fun i => x i ^ e i).prod = (List.ofFn fun i => φ (x i) ^ e i).prod
  rw [map_list_prod, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun i => by
    change Φ (x i ^ e i) = φ (x i) ^ e i
    rw [map_pow]; rfl)

end Hom

end GoodReductionJacobian.RelativeGroupLaw.LevelDescentAux

open GoodReductionJacobian.RelativeGroupLaw.LevelDescentAux in
theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X A' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hcmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ c =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1)
    {m : ℕ} (n : ℕ) (P : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (P' : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) f')
    (hP : ∀ i, (P' i).1 ≫ c = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (P i).1)
    (hindep' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S' →+* K) (c₁ c₂ : Fin m → Fin n),
      L'.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (c₁ i : ℕ)) =
        L'.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (c₂ i : ℕ)) →
        c₁ = c₂)
    (hspan' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S' →+* K) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sK)) f'),
      L'.nsmul (Spec.map (CommRingCat.ofHom sK)) n Q = L'.one (Spec.map (CommRingCat.ofHom sK)) →
        ∃ e : Fin m → Fin n,
          L'.finComb (Spec.map (CommRingCat.ofHom sK))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (e i : ℕ)) = Q) :
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c₁ c₂ : Fin m → Fin n),
      L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c₁ i : ℕ)) =
        L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c₂ i : ℕ)) →
        c₁ = c₂) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f),
      L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ e : Fin m → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (e i : ℕ)) = Q) := by
  classical
  set ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S S')) with hι

  have main : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (sK : S' →+* K) (jj : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
        (hB : jj ≫ Spec.map (CommRingCat.ofHom sk) = Spec.map (CommRingCat.ofHom sK) ≫ ι),
        (∀ q₁ q₂ : Spec (CommRingCat.of k) ⟶ X, jj ≫ q₁ = jj ≫ q₂ → q₁ = q₂) := by
    intro k _ _ sk
    obtain ⟨K, _, _, j, sK, hsK⟩ := Module.FaithfullyFlat.exists_ringHom_isAlgClosed_comp_algebraMap_eq S' k sk
    refine ⟨K, inferInstance, inferInstance, sK, Spec.map (CommRingCat.ofHom j), ?_, ?_⟩
    · rw [hι, ← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun r : S →+* K => Spec.map (CommRingCat.ofHom r)) hsK.symm
    ·
      intro q₁ q₂ h
      letI : Algebra k K := j.toAlgebra
      haveI : Module.FaithfullyFlat k K := inferInstance
      have hcof : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] K)) ≫
            Spec.map (CommRingCat.ofHom j) =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : K →ₐ[k] K ⊗[k] K).toRingHom) ≫
            Spec.map (CommRingCat.ofHom j) := by
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext a
        change Algebra.TensorProduct.includeLeftRingHom (algebraMap k K a) =
          (Algebra.TensorProduct.includeRight : K →ₐ[k] K ⊗[k] K) (algebraMap k K a)
        rw [AlgHom.commutes]
        exact (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] K).commutes a
      have hex := AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat (B := k) (B' := K)
        (Spec.map (CommRingCat.ofHom j) ≫ q₂) (by rw [← Category.assoc, ← Category.assoc, hcof])
      exact hex.unique h rfl
  refine ⟨?_, ?_⟩
  ·
    intro k _ _ sk c₁ c₂ heq
    obtain ⟨K, _, _, sK, jj, hB, hinj⟩ := main k sk

    set tk := Spec.map (CommRingCat.ofHom sk) with htk
    set tK' := Spec.map (CommRingCat.ofHom sK) with htK'
    let α : SchemeHomOver tk f → SchemeHomOver (tK' ≫ ι) f := fun Q => schemeHomOverComp jj hB Q
    let β : SchemeHomOver tK' f' → SchemeHomOver (tK' ≫ ι) f :=
      fun Q' => ⟨Q'.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, Q'.2]⟩
    have hαmul : ∀ x y, α (L.mul tk x y) = L.mul (tK' ≫ ι) (α x) (α y) := fun x y => L.mul_natural _ _ jj hB x y
    have hβmul : ∀ x y, β (L'.mul tK' x y) = L.mul (tK' ≫ ι) (β x) (β y) := fun x y => Subtype.ext (hcmul tK' x y)
    have hβinj : Function.Injective β := by
      intro x y h
      apply Subtype.ext
      apply hc.hom_ext
      · exact congrArg Subtype.val h
      · rw [x.2, y.2]

    have hPP : ∀ i, α (schemeHomOverComp tk (Category.comp_id _) (P i)) = β (schemeHomOverComp tK' (Category.comp_id _) (P' i)) := by
      intro i
      apply Subtype.ext
      change jj ≫ (tk ≫ (P i).1) = (tK' ≫ (P' i).1) ≫ c
      rw [Category.assoc, hP i, ← Category.assoc jj, hB, Category.assoc]

    have h1 := congrArg α heq
    rw [map_finComb L L tk (tK' ≫ ι) α hαmul, map_finComb L L tk (tK' ≫ ι) α hαmul] at h1
    simp only [hPP] at h1
    rw [← map_finComb L' L tK' (tK' ≫ ι) β hβmul, ← map_finComb L' L tK' (tK' ≫ ι) β hβmul] at h1
    exact hindep' K sK c₁ c₂ (hβinj h1)
  ·
    intro k _ _ sk
    set tk := Spec.map (CommRingCat.ofHom sk) with htk
    intro Q hQ
    obtain ⟨K, _, _, sK, jj, hB, hinj⟩ := main k sk
    set tK' := Spec.map (CommRingCat.ofHom sK) with htK'
    let α : SchemeHomOver tk f → SchemeHomOver (tK' ≫ ι) f := fun Q => schemeHomOverComp jj hB Q
    let β : SchemeHomOver tK' f' → SchemeHomOver (tK' ≫ ι) f :=
      fun Q' => ⟨Q'.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, Q'.2]⟩
    have hαmul : ∀ x y, α (L.mul tk x y) = L.mul (tK' ≫ ι) (α x) (α y) := fun x y => L.mul_natural _ _ jj hB x y
    have hβmul : ∀ x y, β (L'.mul tK' x y) = L.mul (tK' ≫ ι) (β x) (β y) := fun x y => Subtype.ext (hcmul tK' x y)
    have hβinj : Function.Injective β := by
      intro x y h
      apply Subtype.ext
      apply hc.hom_ext
      · exact congrArg Subtype.val h
      · rw [x.2, y.2]
    have hαinj : Function.Injective α := by
      intro x y h
      apply Subtype.ext
      exact hinj x.1 y.1 (congrArg Subtype.val h)
    have hPP : ∀ i, α (schemeHomOverComp tk (Category.comp_id _) (P i)) = β (schemeHomOverComp tK' (Category.comp_id _) (P' i)) := by
      intro i
      apply Subtype.ext
      change jj ≫ (tk ≫ (P i).1) = (tK' ≫ (P' i).1) ≫ c
      rw [Category.assoc, hP i, ← Category.assoc jj, hB, Category.assoc]

    let Q' : SchemeHomOver tK' f' :=
      ⟨hc.lift (α Q).1 tK' (α Q).2, hc.lift_snd _ _ _⟩
    have hβQ' : β Q' = α Q := Subtype.ext (hc.lift_fst _ _ _)

    have hQ' : L'.nsmul tK' n Q' = L'.one tK' := by
      apply hβinj
      rw [map_nsmul L' L tK' (tK' ≫ ι) β hβmul, map_one L' L tK' (tK' ≫ ι) β hβmul, hβQ',
        ← map_nsmul L L tk (tK' ≫ ι) α hαmul, hQ, map_one L L tk (tK' ≫ ι) α hαmul]
    obtain ⟨e, he⟩ := hspan' K sK Q' hQ'
    refine ⟨e, hαinj ?_⟩
    rw [map_finComb L L tk (tK' ≫ ι) α hαmul]
    simp only [hPP]
    rw [← map_finComb L' L tK' (tK' ≫ ι) β hβmul, he, hβQ']

end S_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat (solution)
