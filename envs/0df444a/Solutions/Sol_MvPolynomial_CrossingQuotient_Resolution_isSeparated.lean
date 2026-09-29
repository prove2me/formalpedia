-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/dbc71d50-3f62-5f6f-a00c-f69e8494e366

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient
open scoped TensorProduct

namespace CrossingResolutionL6Sep

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

open MvPolynomial.CrossingQuotient.GlueIndex MvPolynomial.CrossingQuotient.Resolution

local notation "C₀" => CrossingQuotient W t
local notation "X₀" => Resolution t e

theorem isClosedImmersion_mapDesc {A : Type u} [CommRing A] [Algebra W A]
    (r₁ r₂ : C₀ →ₐ[W] A) (i j : Fin e)
    (h : IsPullback (Spec.map (CommRingCat.ofHom r₁.toRingHom))
      (Spec.map (CommRingCat.ofHom r₂.toRingHom)) (Resolution.ι t e i) (Resolution.ι t e j))
    (hφ : Function.Surjective
      (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] A)) :
    IsClosedImmersion (pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j) (toSpec t e)) := by
  let φ : C₀ ⊗[W] C₀ →ₐ[W] A := Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _)
  let f := CommRingCat.ofHom (R := C₀ ⊗[W] C₀) (S := A) φ.toRingHom
  have hφ' : Function.Surjective f.hom := hφ
  have hcl : IsClosedImmersion (Spec.map f) := IsClosedImmersion.spec_of_surjective f hφ'
  have hleft : Spec.map f ≫ Spec.map (CommRingCat.ofHom (R := C₀) (S := C₀ ⊗[W] C₀)
      Algebra.TensorProduct.includeLeftRingHom) = Spec.map (CommRingCat.ofHom r₁.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft r₁ r₂
      (fun _ _ => Commute.all _ _) : (φ.restrictScalars W).comp Algebra.TensorProduct.includeLeft = r₁)
  have hright : Spec.map f ≫ Spec.map (CommRingCat.ofHom (R := C₀) (S := C₀ ⊗[W] C₀)
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := W) (A := C₀) (B := C₀)))) =
      Spec.map (CommRingCat.ofHom r₂.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight r₁ r₂
      (fun _ _ => Commute.all _ _) : φ.comp Algebra.TensorProduct.includeRight = r₂)
  let ε := pullback.congrHom (ι_toSpec t e i) (ι_toSpec t e j)
  have key : pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j) (toSpec t e) =
      h.isoPullback.inv ≫ Spec.map f ≫
        (pullbackSpecIso W (CrossingQuotient W t) (CrossingQuotient W t)).inv ≫ ε.inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, Category.assoc, Category.assoc,
        pullback.congrHom_inv, pullback.lift_fst, Category.comp_id, pullbackSpecIso_inv_fst,
        hleft, h.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, Category.assoc, Category.assoc,
        pullback.congrHom_inv, pullback.lift_snd, Category.comp_id, pullbackSpecIso_inv_snd,
        hright, h.isoPullback_inv_snd]
  rw [key]
  infer_instance

abbrev Qci : AffineTargetMorphismProperty := fun X _ f _ ↦ IsAffine X ∧ Function.Surjective f.appTop

theorem isSeparated_of_blocks
    (hblock : ∀ i j : Fin e,
      IsClosedImmersion (pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j) (toSpec t e))) :
    IsSeparated (toSpec t e) := by
  haveI : Qci.IsLocal := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  have hQ : Qci.diagonal (toSpec t e) :=
    AffineTargetMorphismProperty.diagonal_of_openCover_source (Q := Qci) (toSpec t e)
      (Resolution.openCover t e) fun i j =>
        (HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)).mp (hblock i j)
  exact ⟨(HasAffineProperty.diagonal_iff (P := @IsClosedImmersion) (f := toSpec t e)).mp hQ⟩

section squares

variable {t e}

theorem preimage_opensRange_eq {U : Scheme.{u}} (g : U ⟶ chartScheme t) [IsOpenImmersion g]
    (i j : Fin e)
    (hout : ∀ (P : chartScheme t) (Q : chartScheme t),
      Resolution.ι t e i Q = Resolution.ι t e j P → P ∈ Set.range g)
    (hin : ∀ z : U, ∃ Q : chartScheme t, Resolution.ι t e i Q = Resolution.ι t e j (g z)) :
    Resolution.ι t e j ⁻¹ᵁ (Resolution.ι t e i).opensRange = g.opensRange := by
  ext P
  constructor
  · intro hP
    obtain ⟨Q, hQ⟩ := hP
    exact hout P Q hQ
  · rintro ⟨z, rfl⟩
    exact hin z

theorem isPullback_overlap (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    IsPullback (overlapToChartLeft t) (overlapToChartRight t)
      (Resolution.ι t e i) (Resolution.ι t e ⟨(i : ℕ) + 1, hi⟩) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (glue_condition t e i hi).symm ?_
  apply preimage_opensRange_eq
  · intro P Q hPQ
    obtain ⟨a, ha, hb, z, hza, hzb⟩ := (ι_apply_eq_iff t e Q P).mp hPQ
    cases a with
    | chart k =>
      simp only [chart_le_chart] at ha hb
      exact absurd (congrArg Fin.val (ha.symm.trans hb)) (by simp)
    | overlap k hk =>
      simp only [overlap_le_chart] at ha hb
      have hk' : k = i := by
        rcases ha with h | h
        · exact h.symm
        · exfalso
          rcases hb with h' | h'
          · have := congrArg Fin.val h'; simp at this; omega
          · simp at h'; omega
      subst hk'
      refine ⟨z, ?_⟩
      rw [← hzb, glueMap_overlap_chart_succ]
      rfl
    | torus h =>
      refine ⟨torusToOverlap t i z, ?_⟩
      rw [← hzb, glueMap_torus_chart, ← Scheme.Hom.comp_apply, torusToOverlap_overlapToChartRight]
      rfl
  · intro z
    refine ⟨overlapToChartLeft t z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition]

theorem isPullback_torus (i j : Fin e) (hij : i ≠ j) (h₁ : (j : ℕ) ≠ i + 1) (h₂ : (i : ℕ) ≠ j + 1) :
    IsPullback (torusToChart t i) (torusToChart t j) (Resolution.ι t e i) (Resolution.ι t e j) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [torusToChart_ι, torusToChart_ι]
  apply preimage_opensRange_eq
  · intro P Q hPQ
    obtain ⟨a, ha, hb, z, hza, hzb⟩ := (ι_apply_eq_iff t e Q P).mp hPQ
    cases a with
    | chart k =>
      simp only [chart_le_chart] at ha hb
      exact absurd (ha.symm.trans hb) hij
    | overlap k hk =>
      simp only [overlap_le_chart] at ha hb
      exfalso
      rcases ha with h | h <;> rcases hb with h' | h'
      · exact hij (h.trans h'.symm)
      · exact h₁ (by rw [h]; exact h')
      · exact h₂ (by rw [h']; exact h)
      · exact hij (Fin.ext (by omega))
    | torus h =>
      exact ⟨z, hzb⟩
  · intro z
    refine ⟨torusToChart t i z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, torusToChart_ι, torusToChart_ι]

theorem isPullback_self (i : Fin e) :
    IsPullback (Spec.map (CommRingCat.ofHom (AlgHom.id W C₀).toRingHom))
      (Spec.map (CommRingCat.ofHom (AlgHom.id W C₀).toRingHom))
      (Resolution.ι t e i) (Resolution.ι t e i) := by
  have : Spec.map (CommRingCat.ofHom (AlgHom.id W C₀).toRingHom) = 𝟙 (chartScheme t) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id C₀)) = _
    rw [CommRingCat.ofHom_id]
    exact Spec.map_id _
  rw [this]
  exact IsKernelPair.id_of_mono (Resolution.ι t e i)

end squares

section surjective

variable {e}

theorem eq_mul_invSelf_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x : R)
    [IsLocalization.Away x S] (z : S) :
    ∃ (n : ℕ) (a : R), z = algebraMap R S a * IsLocalization.Away.invSelf (S := S) x ^ n := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (S := S) x z
  refine ⟨n, a, ?_⟩
  rw [← h, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem surjective_lift_left :
    Function.Surjective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom W C₀ (OverlapRing t)) (transitionUp t)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] OverlapRing t) := by
  intro z
  obtain ⟨n, a, rfl⟩ := eq_mul_invSelf_pow (V t) z
  refine ⟨a ⊗ₜ (U t ^ n), ?_⟩
  rw [Algebra.TensorProduct.lift_tmul, map_pow, transitionUp_U]
  rfl

theorem surjective_lift_right :
    Function.Surjective (Algebra.TensorProduct.lift
      (transitionUp t) (IsScalarTower.toAlgHom W C₀ (OverlapRing t))
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] OverlapRing t) := by
  intro z
  obtain ⟨n, a, rfl⟩ := eq_mul_invSelf_pow (V t) z
  refine ⟨(U t ^ n) ⊗ₜ a, ?_⟩
  rw [Algebra.TensorProduct.lift_tmul, map_pow, transitionUp_U, mul_comm]
  rfl

theorem surjective_lift_id :
    Function.Surjective (Algebra.TensorProduct.lift (AlgHom.id W C₀) (AlgHom.id W C₀)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] C₀) := by
  intro a
  exact ⟨a ⊗ₜ 1, by rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, mul_one]⟩

theorem algebraMap_mem_of_xT_yT_mem (S : Subalgebra W (TorusRing t)) (hx : xT t ∈ S)
    (hy : yT t ∈ S) (c : C₀) : algebraMap C₀ (TorusRing t) c ∈ S := by
  obtain ⟨p, rfl⟩ := mk_surjective t c
  have key : (IsScalarTower.toAlgHom W C₀ (TorusRing t)).comp (mk t) =
      MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k) := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [MvPolynomial.aeval_X]
    fin_cases k <;> rfl
  have h1 : algebraMap C₀ (TorusRing t) (mk t p) =
      MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k) p :=
    congrArg (fun φ => φ p) key
  rw [h1]
  have h2 : MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k) p ∈
      (MvPolynomial.aeval (fun k : Fin 2 => (![xT t, yT t] : Fin 2 → TorusRing t) k)).range :=
    ⟨p, rfl⟩
  rw [← Algebra.adjoin_range_eq_range_aeval] at h2
  refine (Algebra.adjoin_le ?_) h2
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact hx
  · exact hy

theorem tinv_mem (S : Subalgebra W (TorusRing t)) {a b : ℕ} (hab : a + 2 ≤ b)
    (hx : xT t * tinv t ^ b ∈ S) (hy : yT t * tT t ^ a ∈ S) : tinv t ∈ S := by
  have htT : tT t ∈ S := S.algebraMap_mem t
  have hprod : xT t * tinv t ^ b * (yT t * tT t ^ a) = tinv t ^ (b - a - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, b = a + 1 + m := ⟨b - a - 1, by omega⟩
    rw [show a + 1 + m - a - 1 = m by omega]
    have h1 := xT_mul_yT t
    have h2 := tT_pow_mul_tinv_pow t (a + 1)
    calc xT t * tinv t ^ (a + 1 + m) * (yT t * tT t ^ a)
        = (xT t * yT t) * tT t ^ a * tinv t ^ (a + 1) * tinv t ^ m := by ring
      _ = tinv t ^ m := by rw [h1, ← pow_succ', h2, one_mul]
  have hm : tinv t ^ (b - a - 1) ∈ S := hprod ▸ S.mul_mem hx hy
  have : tinv t = tinv t ^ (b - a - 1) * tT t ^ (b - a - 2) := by
    obtain ⟨m, hm'⟩ : ∃ m, b - a - 1 = m + 1 := ⟨b - a - 2, by omega⟩
    rw [hm', show b - a - 2 = m by omega, pow_succ, mul_assoc, mul_comm (tinv t) (tT t ^ m),
      ← mul_assoc, tinv_pow_mul_tT_pow, one_mul]
  rw [this]
  exact S.mul_mem hm (S.pow_mem htT _)

theorem surjective_lift_torus (i j : ℕ) (h : i + 2 ≤ j ∨ j + 2 ≤ i) :
    Function.Surjective (Algebra.TensorProduct.lift (torusChart t i) (torusChart t j)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] TorusRing t) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  set S := (Algebra.TensorProduct.lift (torusChart t i) (torusChart t j)
      (fun _ _ => Commute.all _ _) : C₀ ⊗[W] C₀ →ₐ[W] TorusRing t).range
  have hxi : xT t * tinv t ^ i ∈ S := (AlgHom.mem_range _).mpr ⟨U t ⊗ₜ 1, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, torusChart_U]⟩
  have hyi : yT t * tT t ^ i ∈ S := (AlgHom.mem_range _).mpr ⟨V t ⊗ₜ 1, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, torusChart_V]⟩
  have hxj : xT t * tinv t ^ j ∈ S := (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ U t, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, torusChart_U]⟩
  have hyj : yT t * tT t ^ j ∈ S := (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ V t, by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, torusChart_V]⟩
  have htinv : tinv t ∈ S := by
    rcases h with h | h
    · exact tinv_mem t S h hxj hyi
    · exact tinv_mem t S h hxi hyj
  have htT : tT t ∈ S := S.algebraMap_mem t
  have hx : xT t ∈ S := by
    have : xT t = xT t * tinv t ^ i * tT t ^ i := by rw [mul_assoc, tinv_pow_mul_tT_pow, mul_one]
    rw [this]; exact S.mul_mem hxi (S.pow_mem htT _)
  have hy : yT t ∈ S := by
    have : yT t = yT t * tT t ^ i * tinv t ^ i := by rw [mul_assoc, tT_pow_mul_tinv_pow, mul_one]
    rw [this]; exact S.mul_mem hyi (S.pow_mem htinv _)
  intro z _
  obtain ⟨n, c, rfl⟩ := eq_mul_invSelf_pow (S := TorusRing t)
    (algebraMap W (CrossingQuotient W t) t) z
  exact S.mul_mem (algebraMap_mem_of_xT_yT_mem t S hx hy c) (S.pow_mem htinv _)

end surjective

theorem block (i j : Fin e) :
    IsClosedImmersion (pullback.mapDesc (Resolution.ι t e i) (Resolution.ι t e j) (toSpec t e)) := by
  by_cases hij : i = j
  · subst hij
    exact isClosedImmersion_mapDesc t e (AlgHom.id W C₀) (AlgHom.id W C₀) i i
      (isPullback_self i) (surjective_lift_id t)
  by_cases h₁ : (j : ℕ) = i + 1
  · have hi : (i : ℕ) + 1 < e := h₁ ▸ j.2
    obtain rfl : j = ⟨(i : ℕ) + 1, hi⟩ := Fin.ext h₁
    exact isClosedImmersion_mapDesc t e (IsScalarTower.toAlgHom W C₀ (OverlapRing t))
      (transitionUp t) i _ (isPullback_overlap i hi) (surjective_lift_left t)
  by_cases h₂ : (i : ℕ) = j + 1
  · have hj : (j : ℕ) + 1 < e := h₂ ▸ i.2
    obtain rfl : i = ⟨(j : ℕ) + 1, hj⟩ := Fin.ext h₂
    exact isClosedImmersion_mapDesc t e (transitionUp t)
      (IsScalarTower.toAlgHom W C₀ (OverlapRing t)) _ j (isPullback_overlap j hj).flip
      (surjective_lift_right t)
  · have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    exact isClosedImmersion_mapDesc t e (torusChart t i) (torusChart t j) i j
      (isPullback_torus i j hij h₁ h₂) (surjective_lift_torus t i j (by omega))

theorem isSeparated_toSpec : IsSeparated (toSpec t e) := isSeparated_of_blocks t e (block t e)

theorem isSeparated : (Resolution t e).IsSeparated :=
  (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := toSpec t e)).mp (isSeparated_toSpec t e)

end CrossingResolutionL6Sep

open AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient in
theorem solution
    {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    (Resolution t e).IsSeparated ∧ IsSeparated (Resolution.toCrossing t e) := by
  have := CrossingResolutionL6Sep.isSeparated t e
  exact ⟨this, inferInstance⟩

end S_MvPolynomial_CrossingQuotient_Resolution_isSeparated
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isSeparated (solution)
