-- Prove2me | solution 1 for GlobalTheory.SW.NbAvg.sum_nb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:56:53.759395+00:00
-- url     : https://prove2.me/submissions/fc0438f1-bff8-47ba-b605-7c70f7bc0eec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_GlobalTheory_SW_Nbr_move_inv
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW
namespace NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
private theorem one_mem_UJset' {M : ℕ} : (1 : Matrix (Fin n) (Fin n) E) ∈ DH E n M := by
  refine ⟨?_, 1, one_pos, Nat.coprime_one_left _, 0, fun k i => ?_, by simp⟩
  · have h1 : ccT (1 : Matrix (Fin n) (Fin n) E) = 1 := by
      unfold ccT
      rw [Matrix.map_one _ (by simp [cc]) (by simp [cc]), Matrix.transpose_one]
    rw [h1, mul_one]
  · rw [Matrix.zero_apply]
    exact isIntegral_zero
private theorem eq_one_of_mem_DH_zero {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n 0) : h = 1 := by
  obtain ⟨-, s, -, hs, y, -, e⟩ := hh
  rw [(Nat.coprime_zero_right _).1 hs] at e
  simpa [sub_eq_zero] using e
private theorem eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq {M : ℕ} {g : Matrix (Fin n) (Fin n) E} (hg : g ∈ DH E n M) :
    ccT g ∈ DH E n M ∧ ∀ h ∈ DH E n M, g * h ∈ DH E n M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · obtain rfl := eq_one_of_mem_DH_zero hg
    refine ⟨?_, fun h hh => by rw [one_mul]; exact hh⟩
    have hc := hg.1
    rw [mul_one] at hc
    rw [hc]
    exact hg
  · exact (finite_cls_and_stab E n M hM).2.2.2.1.2 g hg
private theorem exists_moves_of_cls_eq {M : ℕ} {a b : Vset E n M}
    (e : (Quot.mk _ a : Cls E n M) = Quot.mk _ b) : ∃ h ∈ DH E n M, Moves h a.1 b.1 := by
  have hq := Quot.eqvGen_exact e
  clear e
  induction hq with
  | rel x y hxy => exact hxy
  | refl x => exact ⟨1, one_mem_UJset', fun v => by rw [Matrix.one_mulVec]⟩
  | symm x y _ ih =>
    obtain ⟨h, hh, m⟩ := ih
    exact ⟨ccT h, (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hh).1, Nbr.move_inv (mul_eq_one_comm.1 hh.1) m⟩
  | trans x y z _ _ ih1 ih2 =>
    obtain ⟨h, hh, m⟩ := ih1
    obtain ⟨k, hk, m'⟩ := ih2
    exact ⟨k * h, (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hk).2 h hh, fun v => by rw [m v, m' (h *ᵥ v), Matrix.mulVec_mulVec]⟩
end NbAvg
end GlobalTheory.SW
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.NbAvg
theorem _root_.solution {M : ℕ} [Fintype (Cls E n M)] {P : Ideal (𝓞 E)} {A : Lt E n}
    (hN : (Nb M P A).Finite) {f : Lt E n → ℂ} (hf : IsClassFn M f) :
    ∑ᶠ X ∈ Nb M P A, f X =
      ∑ c : Cls E n M, ((nbIn M P A (Quot.out c).1).ncard : ℂ) * f (Quot.out c).1 := by
  classical
  rcases isEmpty_or_nonempty (Cls E n M) with hE | hE
  · have h0 : Nb M P A = ∅ := by
      ext X
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hX => hE.false (Quot.mk _ ⟨X, hX.1⟩)
    simp [h0]
  let cl : Lt E n → Cls E n M := fun X =>
    if hX : X ∈ Vset E n M then Quot.mk _ ⟨X, hX⟩ else hE.some
  have hcl : ∀ X (hX : X ∈ Vset E n M), cl X = Quot.mk _ ⟨X, hX⟩ := fun X hX => dif_pos hX
  rw [finsum_mem_eq_finite_toFinset_sum _ hN,
    ← Finset.sum_fiberwise_of_maps_to (s := hN.toFinset) (t := Finset.univ) (g := cl)
      (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hset : ((hN.toFinset.filter fun X => cl X = c : Finset (Lt E n)) : Set (Lt E n)) =
      nbIn M P A (Quot.out c).1 := by
    ext X
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, nbIn]
    constructor
    · rintro ⟨hX, hc⟩
      exact ⟨hX, exists_moves_of_cls_eq ((Quot.out_eq c).trans ((hcl X hX.1).symm.trans hc).symm)⟩
    · rintro ⟨hX, h, hh, m⟩
      refine ⟨hX, ?_⟩
      rw [hcl X hX.1]
      exact (Quot.sound (⟨h, hh, m⟩ : ∃ h ∈ DH E n M, Moves h (Quot.out c).1 X)).symm.trans
        (Quot.out_eq c)
  have hval : ∀ X ∈ hN.toFinset.filter (fun X => cl X = c), f X = f (Quot.out c).1 := by
    intro X hX
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hX
    obtain ⟨h, hh, m⟩ := exists_moves_of_cls_eq ((Quot.out_eq c).trans ((hcl X hX.1.1).symm.trans hX.2).symm)
    exact hf h hh _ (Quot.out c).2 X hX.1.1 m
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset, hset]
end GlobalTheory.SW.NbAvg
