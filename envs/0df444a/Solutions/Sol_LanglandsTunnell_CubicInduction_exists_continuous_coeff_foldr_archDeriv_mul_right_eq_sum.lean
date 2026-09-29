-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/89d886ed-73a4-5116-a970-89bae263b993

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL archComponent3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "LanglandsTunnell.CubicInduction.WhittakerBlock"

private theorem isArchSmooth3_zero : WhittakerBlock.IsArchSmooth3 (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := by
  intro g
  exact contDiffOn_const

private theorem isArchSmooth3_add {φ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (hψ : WhittakerBlock.IsArchSmooth3 ψ) : WhittakerBlock.IsArchSmooth3 (φ + ψ) := by
  intro g
  exact (hφ g).add (hψ g)

private theorem isArchSmooth3_smul (c : ℂ) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ) :
    WhittakerBlock.IsArchSmooth3 (c • φ) := by
  intro g
  exact (hφ g).const_smul c

private theorem isArchSmooth3_sum {ι : Type*} (s : Finset ι) {ψ : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hψ : ∀ i ∈ s, WhittakerBlock.IsArchSmooth3 (ψ i)) : WhittakerBlock.IsArchSmooth3 (∑ i ∈ s, ψ i) :=
  Finset.sum_induction ψ WhittakerBlock.IsArchSmooth3 (fun _ _ ha hb => isArchSmooth3_add ha hb) isArchSmooth3_zero hψ

private theorem archDeriv_zero (i j : Fin 3) : archDeriv i j (0 : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0 := by
  funext g
  show deriv (fun _ : ℝ => (0 : ℂ)) 0 = 0
  exact deriv_const _ _

private theorem ofFn_cons {n : ℕ} (a : Fin 3 × Fin 3) (f : Fin n → Fin 3 × Fin 3) :
    List.ofFn (Fin.cons a f : Fin (n + 1) → Fin 3 × Fin 3) = a :: List.ofFn f := by
  rw [List.ofFn_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

private theorem continuous_generalLinearGroup_map_fin3 {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f)

private theorem continuous_realCoord : Continuous StandardKernel.realCoord :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private theorem continuous_realGL_archComponent3 :
    Continuous fun k : AdelicGL 3 (𝓞 ℚ) ℚ => StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ k) := by
  have h₁ := continuous_generalLinearGroup_map_fin3 (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)
    (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)
  have h₂ := continuous_generalLinearGroup_map_fin3 StandardKernel.realCoord continuous_realCoord
  exact h₂.comp h₁

private def coef1 (i j p q : Fin 3) (k : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ((((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ k))⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) p i *
    ((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ k) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) j q : ℂ)

private theorem continuous_coef1 (i j p q : Fin 3) : Continuous fun k => coef1 i j p q k := by
  unfold coef1
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp
      ((Units.continuous_coe_inv.comp continuous_realGL_archComponent3).matrix_elem p i)
  · exact Complex.continuous_ofReal.comp
      ((Units.continuous_val.comp continuous_realGL_archComponent3).matrix_elem j q)

private theorem isArchSmooth3_foldr {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ) :
    ∀ w : List (Fin 3 × Fin 3), WhittakerBlock.IsArchSmooth3 (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ w)
  | [] => hφ
  | ij :: w =>
    isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.1 _ (isArchSmooth3_foldr hφ w) ij.1 ij.2

private theorem archDeriv_sum {ι : Type*} (s : Finset ι) {ψ : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hψ : ∀ i ∈ s, WhittakerBlock.IsArchSmooth3 (ψ i)) (a b : Fin 3) :
    archDeriv a b (∑ i ∈ s, ψ i) = ∑ i ∈ s, archDeriv a b (ψ i) := by
  classical
  revert hψ
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [archDeriv_zero]
  · intro x s hx ih hψ
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.1 _ _ (hψ x (Finset.mem_insert_self x s))
        (isArchSmooth3_sum s fun i hi => hψ i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hψ i (Finset.mem_insert_of_mem hi)]

private theorem archDeriv_smul (c : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (a b : Fin 3) :
    archDeriv a b (c • φ) = c • archDeriv a b φ :=
  isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.2.1 c φ a b

private theorem archDeriv_translate_foldr {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (k g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) {n : ℕ} (f : Fin n → Fin 3 × Fin 3) :
    archDeriv i j (fun x => List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ (List.ofFn f) (x * k)) g =
      ∑ p : Fin 3, ∑ q : Fin 3, coef1 i j p q k *
        List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ (List.ofFn (Fin.cons (p, q) f)) (g * k) := by
  rw [(isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.2.2.2 _
    (isArchSmooth3_foldr hφ (List.ofFn f)) k).2 g i j]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [ofFn_cons]
  rfl

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock in
theorem solution
    (w : List (Fin 3 × Fin 3)) :
    ∃ coeff : AdelicGL 3 (𝓞 ℚ) ℚ → (Fin w.length → Fin 3 × Fin 3) → ℂ,
      (∀ f : Fin w.length → Fin 3 × Fin 3, Continuous fun k => coeff k f) ∧
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ k g : AdelicGL 3 (𝓞 ℚ) ℚ,
        List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) (fun x => φ (x * k)) w g =
          ∑ f : Fin w.length → Fin 3 × Fin 3,
            coeff k f * List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ (List.ofFn f) (g * k) := by
  induction w with
  | nil =>
    refine ⟨fun _ _ => 1, fun _ => continuous_const, ?_⟩
    intro φ _ k g
    simp
  | cons ij w ih =>
    obtain ⟨c, hc, he⟩ := ih
    refine ⟨fun k f => coef1 ij.1 ij.2 (f 0).1 (f 0).2 k * c k (Fin.tail f),
      fun f => (continuous_coef1 _ _ _ _).mul (hc _), ?_⟩
    intro φ hφ k g
    have hinner : List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) (fun x => φ (x * k)) w =
        ∑ f : Fin w.length → Fin 3 × Fin 3,
          c k f • fun x => List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ (List.ofFn f) (x * k) := by
      funext x
      rw [he φ hφ k x, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
    have hsmooth : ∀ f ∈ (Finset.univ : Finset (Fin w.length → Fin 3 × Fin 3)),
        WhittakerBlock.IsArchSmooth3
          (c k f • fun x => List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ (List.ofFn f) (x * k)) :=
      fun f _ => isArchSmooth3_smul _
        (isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.2.2.2 _
          (isArchSmooth3_foldr hφ (List.ofFn f)) k).1
    show archDeriv ij.1 ij.2 (List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) (fun x => φ (x * k)) w) g = _
    rw [hinner, archDeriv_sum _ hsmooth, Finset.sum_apply]
    simp only [archDeriv_smul, Pi.smul_apply, smul_eq_mul]
    simp only [archDeriv_translate_foldr hφ k g ij.1 ij.2]
    have hre : (∑ f : Fin (ij :: w).length → Fin 3 × Fin 3,
          coef1 ij.1 ij.2 (f 0).1 (f 0).2 k * c k (Fin.tail f) *
            List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ (List.ofFn f) (g * k)) =
        ∑ x : (Fin 3 × Fin 3) × (Fin w.length → Fin 3 × Fin 3),
          coef1 ij.1 ij.2 x.1.1 x.1.2 k * c k x.2 *
            List.foldr (fun ij ψ => archDeriv ij.1 ij.2 ψ) φ (List.ofFn (Fin.cons x.1 x.2)) (g * k) :=
      (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3 × Fin 3) _ _ fun x => by
        simp [Fin.consEquiv, Fin.cons_zero, Fin.tail_cons]).symm
    refine Eq.trans ?_ hre.symm
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun f _ => ?_
    ring

end

end S_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum (solution)
