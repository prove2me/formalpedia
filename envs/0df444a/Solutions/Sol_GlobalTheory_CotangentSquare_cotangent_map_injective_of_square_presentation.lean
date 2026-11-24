-- Prove2me | solution 1 for GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:02.58587+00:00
-- url     : https://prove2.me/submissions/1ec6f8a6-7ba6-4ca8-92d8-e14c654fdbc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPoint
import Theorems.Thm_GlobalTheory_CotangentSquare_pderiv_comb
import Theorems.Thm_GlobalTheory_CotangentSquare_det_ne_zero_of_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.CotangentSquare
open MvPolynomial
variable {O B σ : Type} [CommRing O] [CommRing B]
namespace GlobalTheory.CotangentSquare
theorem _root_.solution : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  intro O B A σ _ _ _ _ _ _ _ _ _ ε x f c hc hsurj hf hker hc2 b hb
  classical
  set Ψ := (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) with hΨ
  let η : MvPolynomial σ B →+* O := (ε : A →+* O).comp (Ψ : MvPolynomial σ B →+* A)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  set q := (RingHom.ker ε).comap Ψ with hq
  have hqmem : ∀ F, F ∈ q ↔ η F = 0 := fun F => by
    rw [hq, Ideal.mem_comap, RingHom.mem_ker, hη]
  have hkerq : RingHom.ker Ψ ≤ q := fun F hF => by
    rw [hqmem, hη, (RingHom.mem_ker).1 hF, map_zero]
  have hηf : ∀ i, η (f i) = 0 := fun i => by rw [hη, hf i, map_zero]
  set K := firstOrderKer η with hK
  have hq2 : q ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun a ha b' hb' => ?_
    rw [hqmem] at ha hb'
    exact ⟨by simp [ha, hb'], fun l => by simp [pderiv_mul, ha, hb']⟩
  have hkerL : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine hker.trans (sup_le_sup_left ?_ _)
    rw [pow_two]; exact Ideal.mul_mono_right hkerq
  have hkerK : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ K := hkerL.trans (sup_le_sup_left hq2 _)
  have hsq : RingHom.ker ε ^ 2 = (q ^ 2).map Ψ := by
    rw [Ideal.map_pow, hq, Ideal.map_comap_of_surjective Ψ hsurj]
  have lift : ∀ (L : Ideal (MvPolynomial σ B)), RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ L →
      ∀ F, Ψ F ∈ L.map Ψ → F ∈ Ideal.span (Set.range f) ⊔ L := by
    intro L hL F hF
    obtain ⟨G, hG, hGF⟩ := (Ideal.mem_map_iff_of_surjective Ψ hsurj).1 hF
    have h1 : F - G ∈ RingHom.ker Ψ := by rw [RingHom.mem_ker, map_sub, hGF, sub_self]
    have h2 : F = (F - G) + G := by ring
    rw [h2]; exact Ideal.add_mem _ (hL h1) (Ideal.mem_sup_right hG)
  have hIB : ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A) ≤ K.map Ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker] at hi
    rw [Ideal.mem_comap]
    have : algebraMap B A i = Ψ (C i) := by simp [hΨ]
    rw [this]
    refine Ideal.mem_map_of_mem _ ⟨?_, fun l => by simp⟩
    rw [hη]; simpa [hΨ] using hi
  let Jac : Matrix σ σ O := fun i l => η (pderiv l (f i))
  have hrow : ∀ j, ∃ g : σ → MvPolynomial σ B, ∀ l,
      (if j = l then c else 0) = ∑ i, η (g i) * Jac i l := by
    intro j
    set F := C (algebraMap O B c) * (X j - C (algebraMap O B (ε (x j)))) with hF
    have ha : x j - algebraMap O A (ε (x j)) ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker]; simp
    have hΨF : Ψ F = c • (x j - algebraMap O A (ε (x j))) := by
      simp [hF, hΨ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    have hmem : Ψ F ∈ K.map Ψ := by
      rw [hΨF]
      refine (sup_le ?_ hIB) (hc2 _ ha)
      rw [hsq]; exact Ideal.map_mono hq2
    have hF2 := lift K hkerK F hmem
    rw [Submodule.mem_sup] at hF2
    obtain ⟨s, hs, k, hk, hsk⟩ := hF2
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine ⟨g, fun l => ?_⟩
    have e1 := pderiv_comb η f g hηf k hk l
    rw [hsk] at e1
    rw [← e1, hF]
    by_cases hjl : j = l
    · subst hjl
      simp [pderiv_X_self, hη, hΨ, ← IsScalarTower.algebraMap_apply]
    · simp [hjl, pderiv_X_of_ne (Ne.symm hjl)]
  choose g hg using hrow
  let N : Matrix σ σ O := fun j i => η (g j i)
  have hNJ : N * Jac = c • (1 : Matrix σ σ O) := by
    ext j l
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ← hg j l]
    split_ifs <;> simp
  have hdet : Jac.det ≠ 0 := det_ne_zero_of_mul_eq hc hNJ
  have hCb : C b ∈ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine lift _ hkerL (C b) ?_
    rw [← hsq]; simpa [hΨ] using hb
  rw [Submodule.mem_sup] at hCb
  obtain ⟨s, hs, k, hk, hsk⟩ := hCb
  obtain ⟨g', rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
  have hv : Matrix.vecMul (fun i => η (g' i)) Jac = 0 := by
    funext l
    have e1 := pderiv_comb η f g' hηf k (hq2 hk) l
    rw [hsk] at e1
    simp only [pderiv_C, map_zero] at e1
    change ∑ i, η (g' i) * Jac i l = 0
    exact e1.symm
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  have hCq : C b ∈ q ^ 2 := by
    rw [← hsk]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => ?_) hk
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (hkerq ?_)
    · rw [hqmem]; exact congrFun hv0 i
    · rw [RingHom.mem_ker]; exact hf i
  let ev : MvPolynomial σ B →ₐ[B] B := aeval (fun j => algebraMap O B (ε (x j)))
  have hev : ((ε : A →+* O).comp (algebraMap B A)).comp (ev : MvPolynomial σ B →+* B) = η := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ev, η, hΨ]
    · intro i; simp [ev, η, hΨ, ← IsScalarTower.algebraMap_apply]
  have hqev : q.map ev ≤ (RingHom.ker ε).comap (algebraMap B A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [hqmem] at hF
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← hF, ← hev]
    rfl
  have : b = ev (C b) := by simp [ev]
  rw [this]
  exact Ideal.pow_right_mono hqev 2 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hCq)
end GlobalTheory.CotangentSquare
