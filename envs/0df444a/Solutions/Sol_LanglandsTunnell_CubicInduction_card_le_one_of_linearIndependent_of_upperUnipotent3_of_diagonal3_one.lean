-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/01a4c3c7-aaa0-5508-b1eb-0da7b7a9c3af

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one

set_option autoImplicit false

noncomputable section

section JoinPiece_Assembly

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField Matrix

section Line

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

private theorem card_le_one_of_forall_eq_smul (e : M) (s : Finset M) (hs : ∀ x ∈ s, ∃ c : K, x = c • e)
    (hind : LinearIndependent K (fun x : ↥s => (x : M))) : s.card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun x hx y hy => ?_
  by_contra hne
  obtain ⟨c, rfl⟩ := hs x hx
  obtain ⟨d, rfl⟩ := hs _ hy
  have hc : c ≠ 0 := by
    rintro rfl
    exact hind.ne_zero ⟨(0 : K) • e, hx⟩ (zero_smul K e)
  have hne' : (⟨c • e, hx⟩ : ↥s) ≠ ⟨d • e, hy⟩ := fun h => hne (congrArg Subtype.val h)
  have hsum : ∑ i ∈ ({⟨c • e, hx⟩, ⟨d • e, hy⟩} : Finset ↥s),
      (if i = ⟨c • e, hx⟩ then d else -c) • (i : M) = 0 := by
    rw [Finset.sum_pair hne', if_pos rfl, if_neg hne'.symm]
    show d • (c • e) + -c • (d • e) = 0
    rw [smul_smul, smul_smul, ← add_smul, show d * c + -c * d = 0 by ring, zero_smul]
  have h0 : (if (⟨d • e, hy⟩ : ↥s) = ⟨c • e, hx⟩ then d else -c) = 0 :=
    linearIndependent_iff'.1 hind _ (fun i => if i = ⟨c • e, hx⟩ then d else -c) hsum _
      (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton_self _)))
  rw [if_neg hne'.symm, neg_eq_zero] at h0
  exact hc h0

end Line

section UpperTriangular

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    ((diagonal3 v a : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun i => (a i : v.adicCompletion ℚ) :=
  rfl

private theorem exists_eq_upperUnipotent3_mul_diagonal3 (g : LocalGL3 v) (h20 : cornerEntry v g = 0)
    (h10 : gl3Entry v g 1 0 = 0) (h21 : gl3Entry v g 2 1 = 0) :
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 x y z * diagonal3 v a := by
  have h20' : g.val 2 0 = 0 := h20
  have h10' : g.val 1 0 = 0 := h10
  have h21' : g.val 2 1 = 0 := h21
  have hdet : g.val.det ≠ 0 := gl3Det_ne_zero v g
  have hexp : g.val.det = g.val 0 0 * g.val 1 1 * g.val 2 2 := by
    rw [Matrix.det_fin_three, h20', h10', h21']
    ring
  rw [hexp] at hdet
  obtain ⟨h01, h22⟩ := mul_ne_zero_iff.1 hdet
  obtain ⟨h00, h11⟩ := mul_ne_zero_iff.1 h01
  refine ⟨g.val 0 1 / g.val 1 1, g.val 1 2 / g.val 2 2, g.val 0 2 / g.val 2 2,
    ![Units.mk0 (g.val 0 0) h00, Units.mk0 (g.val 1 1) h11, Units.mk0 (g.val 2 2) h22], ?_⟩
  apply Units.ext
  rw [Units.val_mul, upperUnipotent3_coe, coe_diagonal3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, h20', h10', h21', h11, h22]

private theorem apply_eq_zero_of_apply_one_eq_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (h1 : f 1 = 0) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0) (h21 : gl3Entry v g 2 1 = 0) : f g = 0 := by
  obtain ⟨x, y, z, a, hg⟩ := exists_eq_upperUnipotent3_mul_diagonal3 v g h20 h10 h21
  rw [hg, ← mul_one (diagonal3 v a), apply_upperUnipotent3_mul_of_mem_principalSeries3 hf,
    apply_diagonal3_mul_of_mem_principalSeries3 hf, h1, mul_zero]

private theorem card_le_one_of_forall_apply_eq_zero (s : Finset (↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ))
    (hs : ∀ Λ ∈ s, ∀ f : ↥(principalSeries3 v (fun _ => 1)),
      (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → gl3Entry v g 2 1 = 0 →
        (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (hind : LinearIndependent ℂ (fun Λ : ↥s => (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ))) :
    s.card ≤ 1 := by
  have hker : ∀ Λ ∈ s, ∀ f : ↥(principalSeries3 v (fun _ => 1)), (f : LocalGL3 v → ℂ) 1 = 0 → Λ f = 0 :=
    fun Λ hΛ f h1 => hs Λ hΛ f fun g h20 h10 h21 => apply_eq_zero_of_apply_one_eq_zero v f.2 h1 g h20 h10 h21
  let e : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (1 : LocalGL3 v) : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ).comp (principalSeries3 v (fun _ => 1)).subtype
  have he : ∀ f : ↥(principalSeries3 v (fun _ => 1)), e f = (f : LocalGL3 v → ℂ) 1 := fun f => rfl
  refine card_le_one_of_forall_eq_smul e s (fun Λ hΛ => ?_) hind
  by_cases hφ : ∃ φ : ↥(principalSeries3 v (fun _ => 1)), (φ : LocalGL3 v → ℂ) 1 ≠ 0
  · obtain ⟨φ, hφ⟩ := hφ
    refine ⟨Λ φ / (φ : LocalGL3 v → ℂ) 1, LinearMap.ext fun f => ?_⟩
    have hsub : Λ (f - ((f : LocalGL3 v → ℂ) 1 / (φ : LocalGL3 v → ℂ) 1) • φ) = 0 := by
      refine hker Λ hΛ _ ?_
      simp [hφ]
    rw [map_sub, map_smul, sub_eq_zero] at hsub
    rw [LinearMap.smul_apply, he, hsub]
    simp only [smul_eq_mul]
    ring
  · push Not at hφ
    refine ⟨0, LinearMap.ext fun f => ?_⟩
    rw [zero_smul, LinearMap.zero_apply]
    exact hker Λ hΛ f (hφ f)

private theorem forall_apply_eq_zero_of_chain (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (l₁ : (∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → gl3Entry v g 2 1 = 0 →
          (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (l₂ : (∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 →
          (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (l₃ : (∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 →
          (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (l₄ : (∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (l₅ : (∀ f : ↥(principalSeries3 v (fun _ => 1)), (∀ g : LocalGL3 v, (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) :
    ∀ f : ↥(principalSeries3 v (fun _ => 1)),
      (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → gl3Entry v g 2 1 = 0 →
        (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0 :=
  l₁ (l₂ (l₃ (l₄ (l₅ fun f hf => by
    rw [show f = 0 from Subtype.ext (funext hf), map_zero]))))

end UpperTriangular

end LanglandsTunnell.CubicInduction

end JoinPiece_Assembly

section JoinPiece_Averaging

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def IsLevel3 (m : ℕ) (κ : LocalGL3 v) : Prop :=
  ∀ i j : Fin 3,
    Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))

private theorem isLevel3_iff (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_iff_sub_one (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j) ≤ WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_one (m : ℕ) : IsLevel3 v m 1 := by
  intro i j
  simp only [gl3Entry, Units.val_one, sub_self, map_zero]
  exact zero_le

private theorem valued_coe_apply_le_one_of_mem_localMaximalCompact3 {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 :=
  hk.1 i j

private theorem isLevel3_mul {m : ℕ} {a b : LocalGL3 v} (ha : IsLevel3 v m a) (hb : IsLevel3 v m b)
    (hbK : b ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : IsLevel3 v m (a * b) := by
  rw [isLevel3_iff_sub_one] at ha hb ⊢
  intro i j
  have hid : ((a * b : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) * (b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) +
        ((b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
    rw [Units.val_mul, sub_mul, one_mul]
    abel
  rw [hid, Matrix.add_apply]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hb i j))
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hbK.1 l j)

private theorem
    isLevel3_inv {m : ℕ} {a : LocalGL3 v} (ha : IsLevel3 v m a) (haK : a ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v m a⁻¹ := by
  rw [isLevel3_iff_sub_one] at ha ⊢
  intro i j
  have hid : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (1 - (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) *
        ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [sub_mul, one_mul, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ?_) (fun l => haK.2 l j)
  rw [← neg_sub, Matrix.neg_apply, Valuation.map_neg]
  exact ha i l

private def levelSubgroup3 (m : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k}
  one_mem' := ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).one_mem, isLevel3_one v m⟩
  mul_mem' := fun {_ _} ⟨haK, ha⟩ ⟨hbK, hb⟩ =>
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem haK hbK, isLevel3_mul v ha hb hbK⟩
  inv_mem' := fun {_} ⟨haK, ha⟩ => ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem haK, isLevel3_inv v ha haK⟩

private theorem mem_levelSubgroup3_iff (m : ℕ) (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v m ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k :=
  Iff.rfl

private theorem mem_localMaximalCompact3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
  hk.1

private theorem
    isLevel3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) : IsLevel3 v m k :=
  hk.2

private theorem mem_levelSubgroup3_of_eq_mul {m : ℕ} {s k κ : LocalGL3 v} (hs : s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (hκ : IsLevel3 v m κ) (h : k = s * κ) : κ ∈ levelSubgroup3 v m := by
  refine (mem_levelSubgroup3_iff v m κ).2 ⟨?_, hκ⟩
  have : κ = s⁻¹ * k := by rw [h, inv_mul_cancel_left]
  rw [this]
  exact (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hs) hk

private theorem isLevel3_of_le {n m : ℕ} (hnm : n ≤ m) {k : LocalGL3 v} (hk : IsLevel3 v m k) : IsLevel3 v n k := by
  intro i j
  refine le_trans (hk i j) ?_
  rw [WithZero.exp_le_exp]
  omega

private theorem levelSubgroup3_le_of_le {n m : ℕ} (hnm : n ≤ m) : levelSubgroup3 v m ≤ levelSubgroup3 v n :=
  fun k hk => (mem_levelSubgroup3_iff v n k).2
    ⟨((mem_levelSubgroup3_iff v m k).1 hk).1, isLevel3_of_le v hnm ((mem_levelSubgroup3_iff v m k).1 hk).2⟩

private theorem isLevel3_zero_of_mem_localMaximalCompact3 {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v 0 k := by
  intro i j
  have h1 : WithZero.exp (-((0 : ℕ) : ℤ)) = 1 := by simp
  rw [h1]
  exact le_trans (Valuation.map_sub _ _ _) (max_le (hk.1 i j) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))

private theorem levelSubgroup3_zero : levelSubgroup3 v 0 = localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  ext k
  exact ⟨fun hk => ((mem_levelSubgroup3_iff v 0 k).1 hk).1,
    fun hk => (mem_levelSubgroup3_iff v 0 k).2 ⟨hk, isLevel3_zero_of_mem_localMaximalCompact3 v hk⟩⟩

private theorem mem_levelSubgroup3_zero_iff (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v 0 ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [levelSubgroup3_zero]

private theorem valued_mul_apply_le3_right {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ 1) (hb : ∀ l, Valued.v (b l j) ≤ C) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ 1 * Valued.v (b l j) := mul_le_mul_left (ha l) _
      _ = Valued.v (b l j) := one_mul _
      _ ≤ C := hb l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem isLevel3_conj {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : IsLevel3 v m κ) : IsLevel3 v m (k * κ * k⁻¹) := by
  rw [isLevel3_iff_sub_one] at hκ ⊢
  intro i j
  have hid : ((k * κ * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) *
          ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
    rw [Units.val_mul, Units.val_mul, sub_mul, one_mul, mul_sub, ← mul_assoc, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3_right v (fun l => hk.1 i l) (fun l => ?_)
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l' => hκ l l') (fun l' => hk.2 l' j)

private theorem mul_mul_inv_mem_levelSubgroup3 {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : κ ∈ levelSubgroup3 v m) : k * κ * k⁻¹ ∈ levelSubgroup3 v m :=
  (mem_levelSubgroup3_iff v m _).2
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hk (mem_localMaximalCompact3_of_mem_levelSubgroup3 v hκ))
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hk),
      isLevel3_conj v hk (isLevel3_of_mem_levelSubgroup3 v hκ)⟩

private theorem valued_mul_apply_le3_mul {C C' : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ C) (hb : ∀ l, Valued.v (b l j) ≤ C') :
    Valued.v ((a * b) i j) ≤ C * C' := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C * C' := fun l => by
    rw [map_mul]
    exact mul_le_mul' (ha l) (hb l)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem le_one_of_le_max_mul {M e : WithZero (Multiplicative ℤ)} (he : e < 1) (h : M ≤ max 1 (M * e)) :
    M ≤ 1 := by
  rcases le_or_gt M 1 with hM | hM
  · exact hM
  · exfalso
    have h' : M ≤ M * e := (le_max_iff.1 h).resolve_left (not_le.2 hM)
    obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 (zero_lt_one.trans hM).ne'
    rcases eq_or_ne e 0 with rfl | he0
    · rw [mul_zero] at h'
      exact absurd h' (not_le.2 (WithZero.zero_lt_coe u))
    · obtain ⟨w, rfl⟩ := WithZero.ne_zero_iff_exists.1 he0
      rw [← WithZero.coe_mul, WithZero.coe_le_coe] at h'
      rw [← WithZero.coe_one, WithZero.coe_lt_coe] at he
      exact absurd ((le_mul_iff_one_le_right' _).1 h') (not_le.2 he)

private theorem exp_neg_one_lt_one : WithZero.exp (-((1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem mem_localMaximalCompact3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h1 := isLevel3_of_le v hn hk
  rw [isLevel3_iff_sub_one] at h1
  refine ⟨fun i j => ?_, ?_⟩
  · have hsplit : (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
        ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j +
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j := by
      simp
    rw [hsplit]
    exact le_trans (Valuation.map_add _ _ _)
      (max_le (le_trans (h1 i j) (exp_neg_one_lt_one).le) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))
  · have hid : ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        1 - ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
      rw [mul_sub, mul_one, Units.inv_mul, sub_sub_cancel]
    have hle : ∀ p : Fin 3 × Fin 3,
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2) ≤
          Finset.univ.sup fun q : Fin 3 × Fin 3 =>
            Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2) :=
      fun p => Finset.le_sup (f := fun q : Fin 3 × Fin 3 =>
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2)) (Finset.mem_univ p)
    have hbound : ∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        max 1 ((Finset.univ.sup fun p : Fin 3 × Fin 3 =>
          Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2)) *
            WithZero.exp (-((1 : ℕ) : ℤ))) := by
      intro i j
      conv_lhs => rw [hid]
      rw [Matrix.sub_apply]
      refine le_trans (Valuation.map_sub _ _ _) (max_le_max (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j) ?_)
      exact valued_mul_apply_le3_mul v (fun l => hle (i, l)) (fun l => h1 l j)
    have hM := le_one_of_le_max_mul (exp_neg_one_lt_one) (Finset.sup_le fun (p : Fin 3 × Fin 3) _ => hbound p.1 p.2)
    exact fun i j => le_trans (hle (i, j)) hM

private theorem mem_levelSubgroup3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ levelSubgroup3 v n :=
  (mem_levelSubgroup3_iff v n k).2 ⟨mem_localMaximalCompact3_of_isLevel3 v hn hk, hk⟩

section Transversal

variable {G : Type*} [Group G]

private def IsTransversal (H H' : Subgroup G) (S : Finset G) : Prop :=
  (∀ s ∈ S, s ∈ H) ∧
    ∀ k ∈ H, ∃! s, s ∈ S ∧ ∃ κ ∈ H', k = s * κ

private theorem sum_eq_of_isTransversal {H H' : Subgroup G} {S S' : Finset G} (hS : IsTransversal H H' S)
    (hS' : IsTransversal H H' S') {φ : G → ℂ}
    (hφ : ∀ s, ∀ κ ∈ H', φ (s * κ) = φ s) :
    ∑ s ∈ S, φ s = ∑ s ∈ S', φ s := by

  have hmatch : ∀ s ∈ S, ∃ s', s' ∈ S' ∧ ∃ κ ∈ H', s = s' * κ :=
    fun s hs => (hS'.2 s (hS.1 s hs)).exists
  refine Finset.sum_bij (fun s hs => (hmatch s hs).choose) (fun s hs => (hmatch s hs).choose_spec.1) ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ heq
    obtain ⟨κ₁, hκ₁, h₁⟩ := (hmatch s₁ hs₁).choose_spec.2
    obtain ⟨κ₂, hκ₂, h₂⟩ := (hmatch s₂ hs₂).choose_spec.2

    have hu := hS.2 _ (hS'.1 _ (hmatch s₁ hs₁).choose_spec.1)
    exact hu.unique ⟨hs₁, κ₁⁻¹, H'.inv_mem hκ₁, eq_mul_inv_of_mul_eq h₁.symm⟩
      ⟨hs₂, κ₂⁻¹, H'.inv_mem hκ₂, heq.trans (eq_mul_inv_of_mul_eq h₂.symm)⟩
  · intro s' hs'
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, -⟩ := hS.2 s' (hS'.1 s' hs')
    refine ⟨s, hs, ?_⟩
    obtain ⟨κ', hκ', h'⟩ := (hmatch s hs).choose_spec.2

    refine (hS'.2 s' (hS'.1 s' hs')).unique
      ⟨(hmatch s hs).choose_spec.1, κ' * κ, H'.mul_mem hκ' hκ, ?_⟩
      ⟨hs', 1, H'.one_mem, (mul_one s').symm⟩
    rw [hsκ, ← mul_assoc, ← h']
  · intro s hs
    obtain ⟨κ, hκ, h⟩ := (hmatch s hs).choose_spec.2
    exact (congrArg φ h).trans (hφ _ κ hκ)

private theorem
    isTransversal_image_mul [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S) {k : G}
    (hk : k ∈ H) : IsTransversal H H' (S.image (fun s => k * s)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact H.mul_mem hk (hS.1 s hs)
  · intro k' hk'
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, huniq⟩ :=
      hS.2 (k⁻¹ * k') (H.mul_mem (H.inv_mem hk) hk')
    refine ⟨k * s, ⟨Finset.mem_image_of_mem _ hs, κ, hκ, ?_⟩, ?_⟩
    · rw [mul_assoc, ← hsκ, mul_inv_cancel_left]
    · rintro t ⟨ht, κ', hκ', hκ'eq⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht
      have : s' = s := huniq s' ⟨hs', κ', hκ', by rw [hκ'eq, mul_assoc, inv_mul_cancel_left]⟩
      rw [this]

private theorem isTransversal_image_inv [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S)
    (hN : ∀ k ∈ H, ∀ κ ∈ H', k * κ * k⁻¹ ∈ H') :
    IsTransversal H H' (S.image (fun s => s⁻¹)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact H.inv_mem (hS.1 s hs)
  · intro k hk
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, huniq⟩ := hS.2 k⁻¹ (H.inv_mem hk)
    refine ⟨s⁻¹, ⟨Finset.mem_image_of_mem _ hs, _,
      hN s (hS.1 s hs) _ (H'.inv_mem hκ), ?_⟩, ?_⟩
    · rw [← inv_inv k, hsκ]
      group
    · rintro t ⟨ht, κ', hκ', hk'⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ht
      have hus : u = s :=
        huniq u ⟨hu, _, hN u⁻¹ (H.inv_mem (hS.1 u hu)) _ (H'.inv_mem hκ'), by rw [hk']; group⟩
      rw [hus]

end Transversal

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def levelAvg (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun g => (S.card : ℂ)⁻¹ * ∑ s ∈ S, f (g * s)

private theorem levelAvg_apply (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    levelAvg v S f g = (S.card : ℂ)⁻¹ * ∑ s ∈ S, f (g * s) :=
  rfl

private theorem levelAvg_eq_of_isTransversal {H H' : Subgroup (LocalGL3 v)} {S S' : Finset (LocalGL3 v)}
    (hS : IsTransversal H H' S) (hS' : IsTransversal H H' S') {f : LocalGL3 v → ℂ}
    (hf : ∀ κ ∈ H', ∀ g, f (g * κ) = f g) :
    levelAvg v S f = levelAvg v S' f := by
  have hcard : (S.card : ℂ) = S'.card := by
    have h := sum_eq_of_isTransversal hS hS' (φ := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
    simpa using h
  funext g
  rw [levelAvg_apply, levelAvg_apply, hcard]
  congr 1
  exact sum_eq_of_isTransversal hS hS' (φ := fun s => f (g * s))
    (fun s κ hκ => by simp only [← mul_assoc]; exact hf κ hκ (g * s))

private theorem levelAvg_mul_of_isTransversal {H H' : Subgroup (LocalGL3 v)} {S : Finset (LocalGL3 v)}
    (hS : IsTransversal H H' S) {f : LocalGL3 v → ℂ} (hf : ∀ κ ∈ H', ∀ g, f (g * κ) = f g) {k : LocalGL3 v}
    (hk : k ∈ H) (g : LocalGL3 v) : levelAvg v S f (g * k) = levelAvg v S f g := by
  classical
  have himg : levelAvg v (S.image (fun s => k * s)) f g = levelAvg v S f (g * k) := by
    rw [levelAvg_apply, levelAvg_apply, Finset.card_image_of_injective _ (mul_right_injective k),
      Finset.sum_image (fun _ _ _ _ h => mul_right_injective k h)]
    simp only [mul_assoc]
  rw [← himg, levelAvg_eq_of_isTransversal v (isTransversal_image_mul hS hk) hS hf]

private abbrev IsTransversal3 (n m : ℕ) (S : Finset (LocalGL3 v)) : Prop :=
  IsTransversal (levelSubgroup3 v n) (levelSubgroup3 v m) S

private theorem levelSubgroup3_normalizes (n m : ℕ) :
    ∀ k ∈ levelSubgroup3 v n, ∀ κ ∈ levelSubgroup3 v m, k * κ * k⁻¹ ∈ levelSubgroup3 v m :=
  fun _ hk _ hκ => mul_mul_inv_mem_levelSubgroup3 v (mem_localMaximalCompact3_of_mem_levelSubgroup3 v hk) hκ

private theorem levelAvg_eq_smul_sum (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) :
    levelAvg v S f = (S.card : ℂ)⁻¹ • ∑ s ∈ S, gl3AmbientRightTranslate (R := ℂ) s f := by
  funext g
  simp [levelAvg, Finset.sum_apply]

private theorem levelAvg_mem_principalSeries3 (S : Finset (LocalGL3 v)) {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) : levelAvg v S f ∈ principalSeries3 v χ := by
  rw [levelAvg_eq_smul_sum]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun s _ => rightTranslate_mem_principalSeries3 hf s))

private noncomputable def levelAvgLin (S : Finset (LocalGL3 v)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) :=
  (S.card : ℂ)⁻¹ • ∑ s ∈ S,
    (gl3AmbientRightTranslate (R := ℂ) s).restrict (p := principalSeries3 v χ) (q := principalSeries3 v χ)
      (fun _ hf => rightTranslate_mem_principalSeries3 hf s)

private theorem coe_levelAvgLin_apply (S : Finset (LocalGL3 v)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) :
    ((levelAvgLin v S χ f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) = levelAvg v S f := by
  rw [levelAvg_eq_smul_sum]
  simp [levelAvgLin, LinearMap.sum_apply]

end LanglandsTunnell.CubicInduction

end JoinPiece_Averaging

section JoinPiece_Cells

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem upperUnipotent3_mul_upperUnipotent3 (x y z a b c : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) * upperUnipotent3 a b c
      = upperUnipotent3 (x + a) (y + b) (z + c + x * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private def threeCycle : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 0, 1; 1, 0, 0; 0, 1, 0] (by
    simp [Matrix.det_fin_three])

private theorem threeCycle_coe :
    (threeCycle v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(0 : v.adicCompletion ℚ), 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

private def threeCycleInv : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 1, 0; 0, 0, 1; 1, 0, 0] (by
    simp [Matrix.det_fin_three])

private theorem threeCycleInv_coe :
    (threeCycleInv v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(0 : v.adicCompletion ℚ), 1, 0; 0, 0, 1; 1, 0, 0] :=
  rfl

private theorem threeCycle_mul_threeCycleInv : threeCycle v * threeCycleInv v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeCycle_coe, threeCycleInv_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem threeCycleInv_mul_threeCycle : threeCycleInv v * threeCycle v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeCycle_coe, threeCycleInv_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem antidiagonal3_mul_antidiagonal3 : antidiagonal3 v * antidiagonal3 v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiagonal3_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private def cornerCellPoint (y z : v.adicCompletion ℚ) : LocalGL3 v :=
  threeCycle v * upperUnipotent3 0 y z

private def minorCellPoint (u w : v.adicCompletion ℚ) : LocalGL3 v :=
  threeCycleInv v * upperUnipotent3 u 0 w

private def openCellPoint (x y z : v.adicCompletion ℚ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 x y z

private theorem cornerCellPoint_coe (y z : v.adicCompletion ℚ) :
    (cornerCellPoint v y z : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(0 : v.adicCompletion ℚ), 0, 1; 1, 0, z; 0, 1, y] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cornerCellPoint, threeCycle_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem minorCellPoint_coe (u w : v.adicCompletion ℚ) :
    (minorCellPoint v u w : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(0 : v.adicCompletion ℚ), 1, 0; 0, 0, 1; 1, u, w] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorCellPoint, threeCycleInv_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem openCellPoint_coe (x y z : v.adicCompletion ℚ) :
    (openCellPoint v x y z : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(0 : v.adicCompletion ℚ), 0, 1; 0, 1, y; 1, x, z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [openCellPoint, antidiagonal3_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem
    cornerEntry_cornerCellPoint (y z : v.adicCompletion ℚ) : cornerEntry v (cornerCellPoint v y z) = 0 := by
  simp [cornerEntry, gl3Entry, cornerCellPoint_coe]

private theorem gl3Entry_cornerCellPoint_one_zero (y z : v.adicCompletion ℚ) :
    gl3Entry v (cornerCellPoint v y z) 1 0 = 1 := by
  simp [gl3Entry, cornerCellPoint_coe]

private theorem gl3Entry_cornerCellPoint_two_one (y z : v.adicCompletion ℚ) :
    gl3Entry v (cornerCellPoint v y z) 2 1 = 1 := by
  simp [gl3Entry, cornerCellPoint_coe]

private theorem gl3Entry_cornerCellPoint_two_two (y z : v.adicCompletion ℚ) :
    gl3Entry v (cornerCellPoint v y z) 2 2 = y := by
  simp [gl3Entry, cornerCellPoint_coe]

private theorem gl3Entry_cornerCellPoint_one_two (y z : v.adicCompletion ℚ) :
    gl3Entry v (cornerCellPoint v y z) 1 2 = z := by
  simp [gl3Entry, cornerCellPoint_coe]

private theorem lowerMinor_cornerCellPoint (y z : v.adicCompletion ℚ) : lowerMinor v (cornerCellPoint v y z) = 1 := by
  simp [lowerMinor, gl3Entry, cornerCellPoint_coe]

private theorem cornerEntry_minorCellPoint (u w : v.adicCompletion ℚ) : cornerEntry v (minorCellPoint v u w) = 1 := by
  simp [cornerEntry, gl3Entry, minorCellPoint_coe]

private theorem lowerMinor_minorCellPoint (u w : v.adicCompletion ℚ) : lowerMinor v (minorCellPoint v u w) = 0 := by
  simp [lowerMinor, gl3Entry, minorCellPoint_coe]

private theorem
    cellRatio_minorCellPoint_zero (u w : v.adicCompletion ℚ) : cellRatio v (minorCellPoint v u w) 0 = u := by
  simp [cellRatio, gl3Entry, cornerEntry, minorCellPoint_coe]

private theorem
    cellRatio_minorCellPoint_one (u w : v.adicCompletion ℚ) : cellRatio v (minorCellPoint v u w) 1 = w := by
  simp [cellRatio, gl3Entry, cornerEntry, minorCellPoint_coe]

private theorem
    cornerEntry_openCellPoint (x y z : v.adicCompletion ℚ) : cornerEntry v (openCellPoint v x y z) = 1 := by
  simp [cornerEntry, gl3Entry, openCellPoint_coe]

private theorem lowerMinor_openCellPoint (x y z : v.adicCompletion ℚ) : lowerMinor v (openCellPoint v x y z) = -1 := by
  simp [lowerMinor, gl3Entry, openCellPoint_coe]

private theorem outerMinor_openCellPoint (x y z : v.adicCompletion ℚ) : outerMinor v (openCellPoint v x y z) = -y := by
  simp [outerMinor, gl3Entry, openCellPoint_coe]

private theorem
    cellRatio_openCellPoint (x y z : v.adicCompletion ℚ) : cellRatio v (openCellPoint v x y z) = ![x, z, y] := by
  ext i
  fin_cases i <;>
    simp [cellRatio, gl3Entry, cornerEntry, outerMinor, lowerMinor, openCellPoint_coe]

private theorem cornerCellPoint_mul_upperUnipotent3 (y z a b c : v.adicCompletion ℚ) :
    cornerCellPoint v y z * upperUnipotent3 a b c
      = upperUnipotent3 0 a 0 * cornerCellPoint v (y + b) (z + c - a * (y + b)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cornerCellPoint_coe, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem minorCellPoint_mul_upperUnipotent3 (u w a b c : v.adicCompletion ℚ) :
    minorCellPoint v u w * upperUnipotent3 a b c
      = upperUnipotent3 b 0 0 * minorCellPoint v (u + a) (w + c + u * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorCellPoint_coe, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem openCellPoint_mul_upperUnipotent3 (x y z a b c : v.adicCompletion ℚ) :
    openCellPoint v x y z * upperUnipotent3 a b c = openCellPoint v (x + a) (y + b) (z + c + x * b) := by
  rw [openCellPoint, openCellPoint, mul_assoc, upperUnipotent3_mul_upperUnipotent3]

private theorem cornerCellPoint_mul_diagonal3 (y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    cornerCellPoint v y z * diagonal3 v a
      = diagonal3 v ![a 2, a 0, a 1]
          * cornerCellPoint v (y * ((a 2 : v.adicCompletion ℚ) / (a 1 : v.adicCompletion ℚ)))
              (z * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  have h0 : (a 0 : v.adicCompletion ℚ) ≠ 0 := (a 0).ne_zero
  have h1 : (a 1 : v.adicCompletion ℚ) ≠ 0 := (a 1).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cornerCellPoint_coe, diagonal3_coe, Units.val_mul, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    field_simp

private theorem minorCellPoint_mul_diagonal3 (u w : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    minorCellPoint v u w * diagonal3 v a
      = diagonal3 v ![a 1, a 2, a 0]
          * minorCellPoint v (u * ((a 1 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ)))
              (w * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  have h0 : (a 0 : v.adicCompletion ℚ) ≠ 0 := (a 0).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minorCellPoint_coe, diagonal3_coe, Units.val_mul, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    field_simp

private theorem openCellPoint_mul_diagonal3 (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    openCellPoint v x y z * diagonal3 v a
      = diagonal3 v ![a 2, a 1, a 0]
          * openCellPoint v (x * ((a 1 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ)))
              (y * ((a 2 : v.adicCompletion ℚ) / (a 1 : v.adicCompletion ℚ)))
              (z * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  have h0 : (a 0 : v.adicCompletion ℚ) ≠ 0 := (a 0).ne_zero
  have h1 : (a 1 : v.adicCompletion ℚ) ≠ 0 := (a 1).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [openCellPoint_coe, diagonal3_coe, Units.val_mul, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    field_simp

private theorem halfModulus3_cornerCell_conj (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![a 2, a 0, a 1]
      = ((‖(a 2 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem halfModulus3_minorCell_conj (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![a 1, a 2, a 0]
      = ((‖(a 1 : v.adicCompletion ℚ)‖ / ‖(a 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem halfModulus3_openCell_conj (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![a 2, a 1, a 0]
      = ((‖(a 2 : v.adicCompletion ℚ)‖ / ‖(a 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [halfModulus3]

private def IsUpperTriangular (b : LocalGL3 v) : Prop :=
  cornerEntry v b = 0 ∧ gl3Entry v b 1 0 = 0 ∧ gl3Entry v b 2 1 = 0

private theorem exists_isUpperTriangular_mul_cornerCellPoint {g : LocalGL3 v} (hc : cornerEntry v g = 0)
    (h10 : gl3Entry v g 1 0 ≠ 0) (h21 : gl3Entry v g 2 1 ≠ 0) :
    ∃ (b : LocalGL3 v) (y z : v.adicCompletion ℚ), IsUpperTriangular v b ∧ g = b * cornerCellPoint v y z := by
  set y : v.adicCompletion ℚ := gl3Entry v g 2 2 / gl3Entry v g 2 1 with hy
  set z : v.adicCompletion ℚ :=
    (gl3Entry v g 1 2 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 2) / (gl3Entry v g 1 0 * gl3Entry v g 2 1)
    with hz
  refine ⟨g * (upperUnipotent3 0 (-y) (-z) * threeCycleInv v), y, z, ?_, ?_⟩
  · have hc' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 := hc
    have h10' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 ≠ 0 := h10
    have h21' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 ≠ 0 := h21
    simp only [IsUpperTriangular]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [cornerEntry, gl3Entry, Units.val_mul, upperUnipotent3_coe, threeCycleInv_coe] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hc', hy, hz, gl3Entry] <;>
      field_simp <;>
      ring
  · rw [mul_assoc, mul_assoc, cornerCellPoint, ← mul_assoc (threeCycleInv v), threeCycleInv_mul_threeCycle, one_mul,
      upperUnipotent3_mul_upperUnipotent3]
    simp

private theorem exists_isUpperTriangular_mul_minorCellPoint {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0)
    (hl : lowerMinor v g = 0) :
    ∃ (b : LocalGL3 v) (u w : v.adicCompletion ℚ), IsUpperTriangular v b ∧ g = b * minorCellPoint v u w := by
  set u : v.adicCompletion ℚ := cellRatio v g 0 with hu
  set w : v.adicCompletion ℚ := cellRatio v g 1 with hw
  refine ⟨g * (upperUnipotent3 (-u) 0 (-w) * threeCycle v), u, w, ?_, ?_⟩
  · have hc' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := hc
    have hl' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0
          * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1
        - (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1
          * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 := hl
    simp only [IsUpperTriangular]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [cornerEntry, gl3Entry, Units.val_mul, upperUnipotent3_coe, threeCycle_coe] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hu, hw, cellRatio, gl3Entry, cornerEntry] <;>
      field_simp <;>
      first
        | ring1
        | linear_combination hl'
        | linear_combination -hl'
  · rw [mul_assoc, mul_assoc, minorCellPoint, ← mul_assoc (threeCycle v), threeCycle_mul_threeCycleInv, one_mul,
      upperUnipotent3_mul_upperUnipotent3]
    simp

private theorem exists_isUpperTriangular_mul_openCellPoint {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0)
    (hl : lowerMinor v g ≠ 0) :
    ∃ (b : LocalGL3 v) (x y z : v.adicCompletion ℚ), IsUpperTriangular v b ∧ g = b * openCellPoint v x y z := by
  set x : v.adicCompletion ℚ := cellRatio v g 0 with hx
  set y : v.adicCompletion ℚ := cellRatio v g 2 with hy
  set z : v.adicCompletion ℚ := cellRatio v g 1 with hz
  refine ⟨g * (upperUnipotent3 (-x) (-y) (x * y - z) * antidiagonal3 v), x, y, z, ?_, ?_⟩
  · have hc' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := hc
    have hl' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0
          * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1
        - (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1
          * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := hl
    have hl'' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0
          * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1
        - (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0
          * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 ≠ 0 := by
      rwa [mul_comm ((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0)]
    simp only [IsUpperTriangular]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [cornerEntry, gl3Entry, Units.val_mul, upperUnipotent3_coe, antidiagonal3_coe] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hx, hy, hz, cellRatio, gl3Entry, cornerEntry, outerMinor,
        lowerMinor] <;>
      field_simp <;>
      ring
  · rw [mul_assoc, mul_assoc, openCellPoint, ← mul_assoc (antidiagonal3 v), antidiagonal3_mul_antidiagonal3,
      one_mul, upperUnipotent3_mul_upperUnipotent3]
    simp

private def cornerCellProfile (f : LocalGL3 v → ℂ) (y z : v.adicCompletion ℚ) : ℂ := f (cornerCellPoint v y z)

private def minorCellProfile (f : LocalGL3 v → ℂ) (u w : v.adicCompletion ℚ) : ℂ := f (minorCellPoint v u w)

private def openCellProfile (f : LocalGL3 v → ℂ) (x y z : v.adicCompletion ℚ) : ℂ := f (openCellPoint v x y z)

variable {v}

private theorem cornerCellProfile_rightTranslate_upperUnipotent3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (a b c y z : v.adicCompletion ℚ) :
    cornerCellProfile v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 a b c) f) y z
      = cornerCellProfile v f (y + b) (z + c - a * (y + b)) := by
  simp only [cornerCellProfile, gl3AmbientRightTranslate_apply, cornerCellPoint_mul_upperUnipotent3]
  exact apply_upperUnipotent3_mul_of_mem_principalSeries3 hf _ _ _ _

private theorem minorCellProfile_rightTranslate_upperUnipotent3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (a b c u w : v.adicCompletion ℚ) :
    minorCellProfile v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 a b c) f) u w
      = minorCellProfile v f (u + a) (w + c + u * b) := by
  simp only [minorCellProfile, gl3AmbientRightTranslate_apply, minorCellPoint_mul_upperUnipotent3]
  exact apply_upperUnipotent3_mul_of_mem_principalSeries3 hf _ _ _ _

private theorem
    openCellProfile_rightTranslate_upperUnipotent3 (f : LocalGL3 v → ℂ) (a b c x y z : v.adicCompletion ℚ) :
    openCellProfile v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 a b c) f) x y z
      = openCellProfile v f (x + a) (y + b) (z + c + x * b) := by
  simp only [openCellProfile, gl3AmbientRightTranslate_apply, openCellPoint_mul_upperUnipotent3]

private theorem cornerCellProfile_rightTranslate_diagonal3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (y z : v.adicCompletion ℚ) :
    cornerCellProfile v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f) y z
      = torusChar3 v χ ![a 2, a 0, a 1] * halfModulus3 v ![a 2, a 0, a 1]
          * cornerCellProfile v f (y * ((a 2 : v.adicCompletion ℚ) / (a 1 : v.adicCompletion ℚ)))
              (z * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  simp only [cornerCellProfile, gl3AmbientRightTranslate_apply, cornerCellPoint_mul_diagonal3]
  exact apply_diagonal3_mul_of_mem_principalSeries3 hf _ _

private theorem minorCellProfile_rightTranslate_diagonal3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (u w : v.adicCompletion ℚ) :
    minorCellProfile v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f) u w
      = torusChar3 v χ ![a 1, a 2, a 0] * halfModulus3 v ![a 1, a 2, a 0]
          * minorCellProfile v f (u * ((a 1 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ)))
              (w * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  simp only [minorCellProfile, gl3AmbientRightTranslate_apply, minorCellPoint_mul_diagonal3]
  exact apply_diagonal3_mul_of_mem_principalSeries3 hf _ _

private theorem openCellProfile_rightTranslate_diagonal3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (x y z : v.adicCompletion ℚ) :
    openCellProfile v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f) x y z
      = torusChar3 v χ ![a 2, a 1, a 0] * halfModulus3 v ![a 2, a 1, a 0]
          * openCellProfile v f (x * ((a 1 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ)))
              (y * ((a 2 : v.adicCompletion ℚ) / (a 1 : v.adicCompletion ℚ)))
              (z * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  simp only [openCellProfile, gl3AmbientRightTranslate_apply, openCellPoint_mul_diagonal3]
  exact apply_diagonal3_mul_of_mem_principalSeries3 hf _ _

private theorem torusChar3_one_apply (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : torusChar3 v (fun _ => 1) a = 1 := by
  simp [torusChar3]

private theorem cornerEntry_mul_upperUnipotent3 (g : LocalGL3 v) (a b c : v.adicCompletion ℚ) :
    cornerEntry v (g * upperUnipotent3 a b c) = cornerEntry v g := by
  simp [cornerEntry, gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_one_zero (g : LocalGL3 v) (a b c : v.adicCompletion ℚ) :
    gl3Entry v (g * upperUnipotent3 a b c) 1 0 = gl3Entry v g 1 0 := by
  simp [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_two_one (g : LocalGL3 v) (a b c : v.adicCompletion ℚ) :
    gl3Entry v (g * upperUnipotent3 a b c) 2 1 = cornerEntry v g * a + gl3Entry v g 2 1 := by
  simp [cornerEntry, gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerMinor_mul_upperUnipotent3 (g : LocalGL3 v) (a b c : v.adicCompletion ℚ) :
    lowerMinor v (g * upperUnipotent3 a b c) = lowerMinor v g := by
  simp only [lowerMinor, gl3Entry, Units.val_mul, upperUnipotent3_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

variable (v)

private def lowerShearA (c₁ c₂ : v.adicCompletion ℚ) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0, 0; c₁, 1, 0; c₂, 0, 1] (by
    simp [Matrix.det_fin_three])

private theorem lowerShearA_coe (c₁ c₂ : v.adicCompletion ℚ) :
    (lowerShearA v c₁ c₂ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(1 : v.adicCompletion ℚ), 0, 0; c₁, 1, 0; c₂, 0, 1] :=
  rfl

private def lowerShearB (c : v.adicCompletion ℚ) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0, 0; 0, 1, 0; 0, c, 1] (by
    simp [Matrix.det_fin_three])

private theorem lowerShearB_coe (c : v.adicCompletion ℚ) :
    (lowerShearB v c : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(1 : v.adicCompletion ℚ), 0, 0; 0, 1, 0; 0, c, 1] :=
  rfl

private theorem lowerShearA_congruent {n : ℕ} {c₁ c₂ : v.adicCompletion ℚ} (h₁ : Valued.v c₁ ≤ WithZero.exp (-(n : ℤ)))
    (h₂ : Valued.v c₂ ≤ WithZero.exp (-(n : ℤ))) (i j : Fin 3) :
    Valued.v (gl3Entry v (lowerShearA v c₁ c₂) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      ≤ WithZero.exp (-(n : ℤ)) := by
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, lowerShearA_coe] <;> first | simpa using h₁ | simpa using h₂

private theorem lowerShearB_congruent {n : ℕ} {c : v.adicCompletion ℚ} (h : Valued.v c ≤ WithZero.exp (-(n : ℤ)))
    (i j : Fin 3) :
    Valued.v (gl3Entry v (lowerShearB v c) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      ≤ WithZero.exp (-(n : ℤ)) := by
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, lowerShearB_coe]
  simpa using h

private theorem valued_neg_inv_le {n : ℕ} {c : v.adicCompletion ℚ} (hc : WithZero.exp (n : ℤ) ≤ Valued.v c) :
    Valued.v (-c⁻¹) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [Valuation.map_neg, map_inv₀, WithZero.exp_neg]
  exact inv_anti₀ (zero_lt_iff.mpr WithZero.exp_ne_zero) hc

private theorem valued_div_le {n : ℕ} {a c : v.adicCompletion ℚ} (hc : c ≠ 0)
    (h : WithZero.exp (n : ℤ) * Valued.v a ≤ Valued.v c) :
    Valued.v (a / c) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [map_div₀, div_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc)), WithZero.exp_neg]
  calc Valued.v a = (WithZero.exp (n : ℤ))⁻¹ * (WithZero.exp (n : ℤ) * Valued.v a) := by
        rw [inv_mul_cancel_left₀ WithZero.exp_ne_zero]
    _ ≤ (WithZero.exp (n : ℤ))⁻¹ * Valued.v c := mul_le_mul_right h _

private theorem
    ne_zero_of_exp_le {n : ℕ} {c : v.adicCompletion ℚ} (hc : WithZero.exp (n : ℤ) ≤ Valued.v c) : c ≠ 0 := by
  rintro rfl
  simp at hc

variable {v}

private theorem apply_mul_eq_of_level {f : LocalGL3 v → ℂ} {n : ℕ}
    (hn : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k f = f)
    {k : LocalGL3 v}
    (hk : ∀ i j : Fin 3,
      Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
        ≤ WithZero.exp (-(n : ℤ)))
    (g : LocalGL3 v) : f (g * k) = f g := by
  have h := congrFun (hn k hk) g
  simpa [gl3AmbientRightTranslate_apply] using h

private theorem cornerCellProfile_eq_zero_of_large {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ)
    (hZ : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 → f g = 0) :
    ∃ n : ℕ, ∀ y z : v.adicCompletion ℚ,
      (WithZero.exp (n : ℤ) ≤ Valued.v y ∨ WithZero.exp (n : ℤ) * max 1 (Valued.v y) ≤ Valued.v z) →
        cornerCellProfile v f y z = 0 := by
  obtain ⟨n, hn⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f hf
  refine ⟨n, fun y z h => ?_⟩
  rcases h with hy | hz
  · have hy0 : y ≠ 0 := ne_zero_of_exp_le v hy
    rw [cornerCellProfile, ← apply_mul_eq_of_level hn (lowerShearB_congruent v (valued_neg_inv_le v hy))]
    refine hZ _ ?_ ?_
    · simp [cornerEntry, gl3Entry, Units.val_mul, cornerCellPoint_coe, lowerShearB_coe, Matrix.mul_apply,
        Fin.sum_univ_three]
    · simp [gl3Entry, Units.val_mul, cornerCellPoint_coe, lowerShearB_coe, Matrix.mul_apply, Fin.sum_univ_three,
        hy0]
  · have hz1 : WithZero.exp (n : ℤ) ≤ Valued.v z :=
      le_trans (le_mul_of_one_le_right' (le_max_left 1 (Valued.v y))) hz
    have hz2 : WithZero.exp (n : ℤ) * Valued.v y ≤ Valued.v z :=
      le_trans (mul_le_mul_right (le_max_right 1 (Valued.v y)) _) hz
    have hz0 : z ≠ 0 := ne_zero_of_exp_le v hz1
    rw [cornerCellProfile, ← apply_mul_eq_of_level hn
      (lowerShearA_congruent v (valued_div_le v hz0 hz2) (valued_neg_inv_le v hz1))]
    refine hZ _ ?_ ?_
    · simp [cornerEntry, gl3Entry, Units.val_mul, cornerCellPoint_coe, lowerShearA_coe, Matrix.mul_apply,
        Fin.sum_univ_three]
      field_simp
      ring
    · simp [gl3Entry, Units.val_mul, cornerCellPoint_coe, lowerShearA_coe, Matrix.mul_apply, Fin.sum_univ_three,
        hz0]

private theorem minorCellProfile_eq_zero_of_large {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (hZ : ∀ g : LocalGL3 v, cornerEntry v g = 0 → f g = 0) :
    ∃ n : ℕ, ∀ u w : v.adicCompletion ℚ,
      (WithZero.exp (n : ℤ) ≤ Valued.v u ∨ WithZero.exp (n : ℤ) ≤ Valued.v w) → minorCellProfile v f u w = 0 := by
  obtain ⟨n, hn⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f hf
  have h0 : Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp (-(n : ℤ)) := by simp
  refine ⟨n, fun u w h => ?_⟩
  rcases h with hu | hw
  · have hu0 : u ≠ 0 := ne_zero_of_exp_le v hu
    rw [minorCellProfile, ← apply_mul_eq_of_level hn (lowerShearA_congruent v (valued_neg_inv_le v hu) h0)]
    refine hZ _ ?_
    simp [cornerEntry, gl3Entry, Units.val_mul, minorCellPoint_coe, lowerShearA_coe, Matrix.mul_apply,
      Fin.sum_univ_three, hu0]
  · have hw0 : w ≠ 0 := ne_zero_of_exp_le v hw
    rw [minorCellProfile, ← apply_mul_eq_of_level hn (lowerShearA_congruent v h0 (valued_neg_inv_le v hw))]
    refine hZ _ ?_
    simp [cornerEntry, gl3Entry, Units.val_mul, minorCellPoint_coe, lowerShearA_coe, Matrix.mul_apply,
      Fin.sum_univ_three, hw0]

private theorem openCellProfile_eq_zero_of_large {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (hZ : ∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → f g = 0) :
    ∃ n : ℕ, ∀ x y z : v.adicCompletion ℚ,
      (WithZero.exp (n : ℤ) ≤ Valued.v x ∨ WithZero.exp (n : ℤ) ≤ Valued.v y ∨
          WithZero.exp (n : ℤ) ≤ Valued.v z) →
        openCellProfile v f x y z = 0 := by
  obtain ⟨n, hn⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f hf
  have h0 : Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp (-(n : ℤ)) := by simp
  refine ⟨n, fun x y z h => ?_⟩
  rcases h with hx | hy | hz
  · have hx0 : x ≠ 0 := ne_zero_of_exp_le v hx
    rw [openCellProfile, ← apply_mul_eq_of_level hn (lowerShearA_congruent v (valued_neg_inv_le v hx) h0)]
    refine hZ _ ?_
    simp [cornerEntry, gl3Entry, lowerMinor, Units.val_mul, openCellPoint_coe, lowerShearA_coe, Matrix.mul_apply,
      Fin.sum_univ_three, hx0]
  · have hy0 : y ≠ 0 := ne_zero_of_exp_le v hy
    rw [openCellProfile, ← apply_mul_eq_of_level hn (lowerShearB_congruent v (valued_neg_inv_le v hy))]
    refine hZ _ ?_
    simp [cornerEntry, gl3Entry, lowerMinor, Units.val_mul, openCellPoint_coe, lowerShearB_coe, Matrix.mul_apply,
      Fin.sum_univ_three, hy0]
  · have hz0 : z ≠ 0 := ne_zero_of_exp_le v hz
    rw [openCellProfile, ← apply_mul_eq_of_level hn (lowerShearA_congruent v h0 (valued_neg_inv_le v hz))]
    refine hZ _ ?_
    simp [cornerEntry, gl3Entry, lowerMinor, Units.val_mul, openCellPoint_coe, lowerShearA_coe, Matrix.mul_apply,
      Fin.sum_univ_three, hz0]

private def UpperTriangularFactors : Prop :=
  ∀ b : LocalGL3 v, cornerEntry v b = 0 → gl3Entry v b 1 0 = 0 → gl3Entry v b 2 1 = 0 →
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ), b = upperUnipotent3 x y z * diagonal3 v a

private theorem apply_mul_eq_zero_of_isUpperTriangular (hfac : UpperTriangularFactors (v := v))
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    {b : LocalGL3 v} (hb : IsUpperTriangular v b) {g : LocalGL3 v} (hg : f g = 0) : f (b * g) = 0 := by
  obtain ⟨x, y, z, a, rfl⟩ := hfac b hb.1 hb.2.1 hb.2.2
  rw [mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, apply_diagonal3_mul_of_mem_principalSeries3 hf,
    hg, mul_zero]

private theorem apply_eq_zero_of_cornerEntry_eq_zero (hfac : UpperTriangularFactors (v := v))
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hZ : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 → f g = 0)
    (hcell : ∀ y z : v.adicCompletion ℚ, f (threeCycle v * upperUnipotent3 0 y z) = 0)
    {g : LocalGL3 v} (hg : cornerEntry v g = 0) : f g = 0 := by
  by_cases h : gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0
  · exact hZ g hg h
  · obtain ⟨b, y, z, hb, rfl⟩ :=
      exists_isUpperTriangular_mul_cornerCellPoint v hg (left_ne_zero_of_mul h) (right_ne_zero_of_mul h)
    exact apply_mul_eq_zero_of_isUpperTriangular hfac hf hb (hcell y z)

private theorem apply_eq_zero_of_cornerEntry_mul_lowerMinor_eq_zero (hfac : UpperTriangularFactors (v := v))
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hZ : ∀ g : LocalGL3 v, cornerEntry v g = 0 → f g = 0)
    (hcell : ∀ u w : v.adicCompletion ℚ, f (threeCycleInv v * upperUnipotent3 u 0 w) = 0)
    {g : LocalGL3 v} (hg : cornerEntry v g * lowerMinor v g = 0) : f g = 0 := by
  by_cases hc : cornerEntry v g = 0
  · exact hZ g hc
  · have hl : lowerMinor v g = 0 := (mul_eq_zero.mp hg).resolve_left hc
    obtain ⟨b, u, w, hb, rfl⟩ := exists_isUpperTriangular_mul_minorCellPoint v hc hl
    exact apply_mul_eq_zero_of_isUpperTriangular hfac hf hb (hcell u w)

private theorem apply_eq_zero_of_forall_openCell (hfac : UpperTriangularFactors (v := v))
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hZ : ∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → f g = 0)
    (hcell : ∀ x y z : v.adicCompletion ℚ, f (antidiagonal3 v * upperUnipotent3 x y z) = 0)
    (g : LocalGL3 v) : f g = 0 := by
  by_cases h : cornerEntry v g * lowerMinor v g = 0
  · exact hZ g h
  · obtain ⟨b, x, y, z, hb, rfl⟩ :=
      exists_isUpperTriangular_mul_openCellPoint v (left_ne_zero_of_mul h) (right_ne_zero_of_mul h)
    exact apply_mul_eq_zero_of_isUpperTriangular hfac hf hb (hcell x y z)

variable (v)

private def torusDifference (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  f - (halfModulus3 v a)⁻¹ • gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f

private theorem halfModulus3_ne_zero (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : halfModulus3 v a ≠ 0 := by
  simp [halfModulus3, (a 0).ne_zero, (a 2).ne_zero]

private theorem torusDifference_mem_principalSeries3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) :
    torusDifference v a f ∈ principalSeries3 v χ :=
  (principalSeries3 v χ).sub_mem hf ((principalSeries3 v χ).smul_mem _ (rightTranslate_mem_principalSeries3 hf _))

private theorem cornerCellProfile_torusDifference {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (y z : v.adicCompletion ℚ) :
    cornerCellProfile v (torusDifference v a f) y z
      = cornerCellProfile v f y z
        - (halfModulus3 v a)⁻¹ * (torusChar3 v χ ![a 2, a 0, a 1] * halfModulus3 v ![a 2, a 0, a 1])
          * cornerCellProfile v f (y * ((a 2 : v.adicCompletion ℚ) / (a 1 : v.adicCompletion ℚ)))
              (z * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  have h := cornerCellProfile_rightTranslate_diagonal3 hf a y z
  simp only [cornerCellProfile] at h ⊢
  simp only [torusDifference, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f (cornerCellPoint v y z) = _ from h]
  ring

private theorem minorCellProfile_torusDifference {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (u w : v.adicCompletion ℚ) :
    minorCellProfile v (torusDifference v a f) u w
      = minorCellProfile v f u w
        - (halfModulus3 v a)⁻¹ * (torusChar3 v χ ![a 1, a 2, a 0] * halfModulus3 v ![a 1, a 2, a 0])
          * minorCellProfile v f (u * ((a 1 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ)))
              (w * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  have h := minorCellProfile_rightTranslate_diagonal3 hf a u w
  simp only [minorCellProfile] at h ⊢
  simp only [torusDifference, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f (minorCellPoint v u w) = _ from h]
  ring

private theorem openCellProfile_torusDifference {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) :
    openCellProfile v (torusDifference v a f) x y z
      = openCellProfile v f x y z
        - (halfModulus3 v a)⁻¹ * (torusChar3 v χ ![a 2, a 1, a 0] * halfModulus3 v ![a 2, a 1, a 0])
          * openCellProfile v f (x * ((a 1 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ)))
              (y * ((a 2 : v.adicCompletion ℚ) / (a 1 : v.adicCompletion ℚ)))
              (z * ((a 2 : v.adicCompletion ℚ) / (a 0 : v.adicCompletion ℚ))) := by
  have h := openCellProfile_rightTranslate_diagonal3 hf a x y z
  simp only [openCellProfile] at h ⊢
  simp only [torusDifference, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f (openCellPoint v x y z) = _ from h]
  ring

private def residueCard : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

private def firstTorusElement : Fin 3 → (v.adicCompletion ℚ)ˣ := ![uniformizerUnit ℚ v, 1, 1]

private def secondTorusElement : Fin 3 → (v.adicCompletion ℚ)ˣ := ![1, 1, uniformizerUnit ℚ v]

private theorem cornerCellProfile_torusDifference_first {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    (y z : v.adicCompletion ℚ) :
    cornerCellProfile v (torusDifference v (firstTorusElement v) f) y z
      = cornerCellProfile v f y z
        - residueCard v * cornerCellProfile v f y (z / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) := by
  rw [cornerCellProfile_torusDifference v hf, torusChar3_one_apply]
  simp [firstTorusElement, halfModulus3_uniformizerUnit, halfModulus3_one_uniformizerUnit_one, residueCard,
    div_eq_mul_inv]

private theorem cornerCellProfile_torusDifference_second {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    (y z : v.adicCompletion ℚ) :
    cornerCellProfile v (torusDifference v (secondTorusElement v) f) y z
      = cornerCellProfile v f y z
        - (residueCard v)⁻¹ ^ 2
          * cornerCellProfile v f (y * (uniformizerUnit ℚ v : v.adicCompletion ℚ))
              (z * (uniformizerUnit ℚ v : v.adicCompletion ℚ)) := by
  rw [cornerCellProfile_torusDifference v hf, torusChar3_one_apply]
  simp [secondTorusElement, halfModulus3_uniformizerUnit, halfModulus3_one_one_uniformizerUnit, residueCard]
  left
  ring1

private theorem minorCellProfile_torusDifference_first {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    (u w : v.adicCompletion ℚ) :
    minorCellProfile v (torusDifference v (firstTorusElement v) f) u w
      = minorCellProfile v f u w
        - residueCard v ^ 2
          * minorCellProfile v f (u / (uniformizerUnit ℚ v : v.adicCompletion ℚ))
              (w / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) := by
  rw [minorCellProfile_torusDifference v hf, torusChar3_one_apply]
  simp [firstTorusElement, halfModulus3_uniformizerUnit, halfModulus3_one_one_uniformizerUnit, residueCard,
    div_eq_mul_inv]
  left
  ring1

private theorem minorCellProfile_torusDifference_second {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    (u w : v.adicCompletion ℚ) :
    minorCellProfile v (torusDifference v (secondTorusElement v) f) u w
      = minorCellProfile v f u w
        - (residueCard v)⁻¹ * minorCellProfile v f u (w * (uniformizerUnit ℚ v : v.adicCompletion ℚ)) := by
  rw [minorCellProfile_torusDifference v hf, torusChar3_one_apply]
  simp [secondTorusElement, halfModulus3_one_one_uniformizerUnit, halfModulus3_one_uniformizerUnit_one, residueCard]

private theorem openCellProfile_torusDifference_first {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    (x y z : v.adicCompletion ℚ) :
    openCellProfile v (torusDifference v (firstTorusElement v) f) x y z
      = openCellProfile v f x y z
        - residueCard v ^ 2
          * openCellProfile v f (x / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) y
              (z / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) := by
  rw [openCellProfile_torusDifference v hf, torusChar3_one_apply]
  simp [firstTorusElement, halfModulus3_uniformizerUnit, halfModulus3_one_one_uniformizerUnit, residueCard,
    div_eq_mul_inv]
  left
  ring1

private theorem openCellProfile_torusDifference_second {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    (x y z : v.adicCompletion ℚ) :
    openCellProfile v (torusDifference v (secondTorusElement v) f) x y z
      = openCellProfile v f x y z
        - (residueCard v)⁻¹ ^ 2
          * openCellProfile v f x (y * (uniformizerUnit ℚ v : v.adicCompletion ℚ))
              (z * (uniformizerUnit ℚ v : v.adicCompletion ℚ)) := by
  rw [openCellProfile_torusDifference v hf, torusChar3_one_apply]
  simp [secondTorusElement, halfModulus3_uniformizerUnit, halfModulus3_one_one_uniformizerUnit, residueCard]
  left
  ring1

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_Cells

section JoinPiece_TransportGeneric

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Transport

variable {G : Type*} [Group G]

private theorem isTransversal_image_conj [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S)
    {k : G} (hH : ∀ g, g ∈ H ↔ k⁻¹ * g * k ∈ H) (hH' : ∀ g, g ∈ H' ↔ k⁻¹ * g * k ∈ H') :
    IsTransversal H H' (S.image fun s => k⁻¹ * s * k) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact (hH s).mp (hS.1 s hs)
  · intro g hg
    have hg' : k * g * k⁻¹ ∈ H := (hH _).mpr (by simpa [mul_assoc] using hg)
    obtain ⟨s, ⟨hs, κ, hκ, hgs⟩, huniq⟩ := hS.2 _ hg'
    refine ⟨k⁻¹ * s * k, ⟨Finset.mem_image.mpr ⟨s, hs, rfl⟩, k⁻¹ * κ * k, (hH' κ).mp hκ, ?_⟩, ?_⟩
    · calc g = k⁻¹ * (k * g * k⁻¹) * k := by simp [mul_assoc]
        _ = k⁻¹ * (s * κ) * k := by rw [hgs]
        _ = k⁻¹ * s * k * (k⁻¹ * κ * k) := by simp [mul_assoc]
    · rintro t ⟨ht, κ', hκ', hgt⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      have hκ'' : k * κ' * k⁻¹ ∈ H' := (hH' _).mpr (by simpa [mul_assoc] using hκ')
      have : s' = s := by
        refine huniq s' ⟨hs', k * κ' * k⁻¹, hκ'', ?_⟩
        calc k * g * k⁻¹ = k * (k⁻¹ * s' * k * κ') * k⁻¹ := by rw [hgt]
          _ = s' * (k * κ' * k⁻¹) := by simp [mul_assoc]
      rw [this]

private theorem sum_mul_right_eq_of_isTransversal [DecidableEq G] {H H' : Subgroup G} {S : Finset G}
    (hS : IsTransversal H H' S) {k : G} (hH : ∀ g, g ∈ H ↔ k⁻¹ * g * k ∈ H)
    (hH' : ∀ g, g ∈ H' ↔ k⁻¹ * g * k ∈ H') {w : G} {f : G → ℂ}
    (hw : ∀ s : G, f (w * s * k) = f (w * (k⁻¹ * s * k)))
    (hf : ∀ s : G, ∀ κ ∈ H', f (w * (s * κ)) = f (w * s)) :
    ∑ s ∈ S, f (w * s * k) = ∑ s ∈ S, f (w * s) := by
  have hinj : Function.Injective fun s : G => k⁻¹ * s * k := by
    intro a b hab
    simpa using hab
  calc ∑ s ∈ S, f (w * s * k) = ∑ s ∈ S, f (w * (k⁻¹ * s * k)) := Finset.sum_congr rfl fun s _ => hw s
    _ = ∑ t ∈ S.image (fun s => k⁻¹ * s * k), f (w * t) := by rw [Finset.sum_image fun _ _ _ _ h => hinj h]
    _ = ∑ s ∈ S, f (w * s) :=
        sum_eq_of_isTransversal (isTransversal_image_conj hS hH hH') hS (φ := fun t => f (w * t)) hf

end Transport

section TransportMore

variable {G : Type*} [Group G]

private theorem isTransversal_image_mul_right [DecidableEq G] {H H' : Subgroup G} {S : Finset G}
    (hS : IsTransversal H H' S) {k : G} (hk : k ∈ H) (hH' : ∀ g, g ∈ H' ↔ k⁻¹ * g * k ∈ H') :
    IsTransversal H H' (S.image fun s => s * k) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact H.mul_mem (hS.1 s hs) hk
  · intro g hg
    have hg' : g * k⁻¹ ∈ H := H.mul_mem hg (H.inv_mem hk)
    obtain ⟨s, ⟨hs, κ, hκ, hgs⟩, huniq⟩ := hS.2 _ hg'
    refine ⟨s * k, ⟨Finset.mem_image.mpr ⟨s, hs, rfl⟩, k⁻¹ * κ * k, (hH' κ).mp hκ, ?_⟩, ?_⟩
    · calc g = g * k⁻¹ * k := by simp
        _ = s * κ * k := by rw [hgs]
        _ = s * k * (k⁻¹ * κ * k) := by simp [mul_assoc]
    · rintro t ⟨ht, κ', hκ', hgt⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht
      have hκ'' : k * κ' * k⁻¹ ∈ H' := (hH' _).mpr (by simpa [mul_assoc] using hκ')
      have : s' = s := by
        refine huniq s' ⟨hs', k * κ' * k⁻¹, hκ'', ?_⟩
        calc g * k⁻¹ = s' * k * κ' * k⁻¹ := by rw [hgt]
          _ = s' * (k * κ' * k⁻¹) := by simp [mul_assoc]
      rw [this]

private theorem forall_mem_iff_conj_mem {H : Subgroup G} {k : G} (h₁ : ∀ g ∈ H, k⁻¹ * g * k ∈ H)
    (h₂ : ∀ g ∈ H, k * g * k⁻¹ ∈ H) : ∀ g, g ∈ H ↔ k⁻¹ * g * k ∈ H := by
  intro g
  refine ⟨h₁ g, fun hg => ?_⟩
  simpa [mul_assoc] using h₂ _ hg

private theorem
    isTransversal_image_conj_mul [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S)
    {k₁ k₂ : G} (hH₁ : ∀ g, g ∈ H ↔ k₁⁻¹ * g * k₁ ∈ H) (hH₁' : ∀ g, g ∈ H' ↔ k₁⁻¹ * g * k₁ ∈ H') (hk₂ : k₂ ∈ H)
    (hH₂' : ∀ g, g ∈ H' ↔ k₂⁻¹ * g * k₂ ∈ H') :
    IsTransversal H H' (S.image fun s => k₁⁻¹ * s * k₁ * k₂) := by
  have h := isTransversal_image_mul_right (isTransversal_image_conj hS hH₁ hH₁') hk₂ hH₂'
  rw [Finset.image_image] at h
  exact h

private theorem injective_conj_mul (k₁ k₂ : G) : Function.Injective fun s : G => k₁⁻¹ * s * k₁ * k₂ := by
  intro a b hab
  simpa using hab

private theorem
    sum_mul_right_eq_of_conj_mul [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S)
    {k₁ k₂ : G} (hH₁ : ∀ g, g ∈ H ↔ k₁⁻¹ * g * k₁ ∈ H) (hH₁' : ∀ g, g ∈ H' ↔ k₁⁻¹ * g * k₁ ∈ H') (hk₂ : k₂ ∈ H)
    (hH₂' : ∀ g, g ∈ H' ↔ k₂⁻¹ * g * k₂ ∈ H') {w : G} {f : G → ℂ}
    (hw : ∀ s : G, f (w * s * (k₁ * k₂)) = f (w * (k₁⁻¹ * s * k₁ * k₂)))
    (hf : ∀ s : G, ∀ κ ∈ H', f (w * (s * κ)) = f (w * s)) :
    ∑ s ∈ S, f (w * s * (k₁ * k₂)) = ∑ s ∈ S, f (w * s) := by
  calc ∑ s ∈ S, f (w * s * (k₁ * k₂)) = ∑ s ∈ S, f (w * (k₁⁻¹ * s * k₁ * k₂)) :=
        Finset.sum_congr rfl fun s _ => hw s
    _ = ∑ t ∈ S.image (fun s => k₁⁻¹ * s * k₁ * k₂), f (w * t) := by
        rw [Finset.sum_image fun _ _ _ _ h => injective_conj_mul k₁ k₂ h]
    _ = ∑ s ∈ S, f (w * s) :=
        sum_eq_of_isTransversal (isTransversal_image_conj_mul hS hH₁ hH₁' hk₂ hH₂') hS (φ := fun t => f (w * t)) hf

end TransportMore

namespace BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem upperUnipotent3_mul_upperUnipotent3_eq_mul (x y z a b c : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) * upperUnipotent3 a b c
      = upperUnipotent3 a b c * upperUnipotent3 x y (z + x * b - a * y) := by
  rw [upperUnipotent3_mul_upperUnipotent3, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem inv_mul_upperUnipotent3_mul (x y z a b c : v.adicCompletion ℚ) :
    (upperUnipotent3 a b c : LocalGL3 v)⁻¹ * upperUnipotent3 x y z * upperUnipotent3 a b c
      = upperUnipotent3 x y (z + x * b - a * y) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul, upperUnipotent3_mul_upperUnipotent3_eq_mul]

private theorem upperUnipotent3_mul_mul_inv (x y z a b c : v.adicCompletion ℚ) :
    (upperUnipotent3 a b c : LocalGL3 v) * upperUnipotent3 x y z * (upperUnipotent3 a b c)⁻¹
      = upperUnipotent3 x y (z + a * y - x * b) := by
  rw [mul_inv_eq_iff_eq_mul, upperUnipotent3_mul_upperUnipotent3, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem threeCycle_mul_upperUnipotent3_stab (a : v.adicCompletion ℚ) :
    threeCycle v * upperUnipotent3 a 0 0 = upperUnipotent3 0 a 0 * threeCycle v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeCycle_coe, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem threeCycleInv_mul_upperUnipotent3_stab (c : v.adicCompletion ℚ) :
    threeCycleInv v * upperUnipotent3 0 c 0 = upperUnipotent3 c 0 0 * threeCycleInv v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeCycleInv_coe, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

variable {v}

private theorem apply_mul_mul_eq_of_mem_principalSeries3 {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    {w k₁ : LocalGL3 v} {p q r : v.adicCompletion ℚ} (hstab : w * k₁ = upperUnipotent3 p q r * w)
    (k₂ s : LocalGL3 v) : f (w * s * (k₁ * k₂)) = f (w * (k₁⁻¹ * s * k₁ * k₂)) := by
  have h : w * s * (k₁ * k₂) = upperUnipotent3 p q r * (w * (k₁⁻¹ * s * k₁ * k₂)) := by
    calc w * s * (k₁ * k₂) = w * k₁ * (k₁⁻¹ * s * k₁ * k₂) := by simp [mul_assoc]
      _ = upperUnipotent3 p q r * (w * (k₁⁻¹ * s * k₁ * k₂)) := by rw [hstab, mul_assoc]
  rw [h, apply_upperUnipotent3_mul_of_mem_principalSeries3 hf]

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_TransportGeneric

section JoinPiece_Transversals

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField

section UnipotentTransversal

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def valuationBall (k : ℤ) : AddSubgroup (v.adicCompletion ℚ) where
  carrier := {x | Valued.v x ≤ WithZero.exp (-k)}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact Valued.v.map_add_le ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact zero_le'
  neg_mem' hx := by simpa only [Set.mem_setOf_eq, Valuation.map_neg] using hx

variable {v} in
private theorem mem_valuationBall_iff {k : ℤ} {x : v.adicCompletion ℚ} :
    x ∈ valuationBall v k ↔ Valued.v x ≤ WithZero.exp (-k) :=
  Iff.rfl

private theorem valuationBall_le_of_le {k m : ℤ} (hkm : k ≤ m) : valuationBall v m ≤ valuationBall v k :=
  fun _ hx => mem_valuationBall_iff.2 (le_trans (mem_valuationBall_iff.1 hx) (WithZero.exp_le_exp.2 (neg_le_neg hkm)))

variable {v} in

private theorem mul_mem_valuationBall {kx ky kz : ℤ} (hk : kz ≤ kx + ky) {x y : v.adicCompletion ℚ}
    (hx : x ∈ valuationBall v kx) (hy : y ∈ valuationBall v ky) : x * y ∈ valuationBall v kz := by
  rw [mem_valuationBall_iff] at hx hy ⊢
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ WithZero.exp (-kx) * WithZero.exp (-ky) := mul_le_mul' hx hy
    _ = WithZero.exp (-kx + -ky) := (WithZero.exp_add _ _).symm
    _ ≤ WithZero.exp (-kz) := WithZero.exp_le_exp.2 (by omega)

private def upperUnipotentSubgroup (Bx By Bz : AddSubgroup (v.adicCompletion ℚ))
    (h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz) : Subgroup (LocalGL3 v) where
  carrier := {g | ∃ x y z, x ∈ Bx ∧ y ∈ By ∧ z ∈ Bz ∧ g = upperUnipotent3 x y z}
  mul_mem' := by
    rintro _ _ ⟨x, y, z, hx, hy, hz, rfl⟩ ⟨x', y', z', hx', hy', hz', rfl⟩
    exact ⟨x + x', y + y', z + z' + x * y', Bx.add_mem hx hx', By.add_mem hy hy',
      Bz.add_mem (Bz.add_mem hz hz') (h x hx y' hy'),
      BruhatCells.upperUnipotent3_mul_upperUnipotent3 v x y z x' y' z'⟩
  one_mem' := ⟨0, 0, 0, Bx.zero_mem, By.zero_mem, Bz.zero_mem, by rw [upperUnipotent3_zero]⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, hx, hy, hz, rfl⟩
    refine ⟨-x, -y, x * y - z, Bx.neg_mem hx, By.neg_mem hy, Bz.sub_mem (h x hx y hy) hz, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [BruhatCells.upperUnipotent3_mul_upperUnipotent3, show x + -x = 0 by ring, show y + -y = 0 by ring,
      show z + (x * y - z) + x * -y = 0 by ring, upperUnipotent3_zero]

variable {v}

private theorem mem_upperUnipotentSubgroup_iff {Bx By Bz : AddSubgroup (v.adicCompletion ℚ)}
    {h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz} {g : LocalGL3 v} :
    g ∈ upperUnipotentSubgroup v Bx By Bz h ↔ ∃ x y z, x ∈ Bx ∧ y ∈ By ∧ z ∈ Bz ∧ g = upperUnipotent3 x y z :=
  Iff.rfl

private theorem upperUnipotent3_eq_upperUnipotent3_iff {x y z x' y' z' : v.adicCompletion ℚ} :
    (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 x' y' z' ↔ x = x' ∧ y = y' ∧ z = z' := by
  refine ⟨fun h => ?_, ?_⟩
  · have h' := congrArg (fun g : LocalGL3 v => (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h
    simp only [upperUnipotent3_coe] at h'
    exact ⟨by simpa using congrFun (congrFun h' 0) 1, by simpa using congrFun (congrFun h' 1) 2,
      by simpa using congrFun (congrFun h' 0) 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem upperUnipotent3_mem_upperUnipotentSubgroup_iff {Bx By Bz : AddSubgroup (v.adicCompletion ℚ)}
    {h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz} {x y z : v.adicCompletion ℚ} :
    upperUnipotent3 x y z ∈ upperUnipotentSubgroup v Bx By Bz h ↔ x ∈ Bx ∧ y ∈ By ∧ z ∈ Bz := by
  refine ⟨fun hmem => ?_, fun ⟨hx, hy, hz⟩ => mem_upperUnipotentSubgroup_iff.2 ⟨x, y, z, hx, hy, hz, rfl⟩⟩
  obtain ⟨x', y', z', hx, hy, hz, heq⟩ := mem_upperUnipotentSubgroup_iff.1 hmem
  obtain ⟨rfl, rfl, rfl⟩ := upperUnipotent3_eq_upperUnipotent3_iff.1 heq
  exact ⟨hx, hy, hz⟩

private theorem forall_mem_bot_mul_mem (By Bz : AddSubgroup (v.adicCompletion ℚ)) :
    ∀ x ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)), ∀ y ∈ By, x * y ∈ Bz := by
  intro x hx y _
  rw [(AddSubgroup.mem_bot).1 hx, zero_mul]
  exact Bz.zero_mem

private theorem forall_mul_mem_bot_mem (Bx Bz : AddSubgroup (v.adicCompletion ℚ)) :
    ∀ x ∈ Bx, ∀ y ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)), x * y ∈ Bz := by
  intro x _ y hy
  rw [(AddSubgroup.mem_bot).1 hy, mul_zero]
  exact Bz.zero_mem

private theorem forall_mem_singleton_zero_mem_bot :
    ∀ r ∈ ({0} : Finset (v.adicCompletion ℚ)), r ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)) := by
  intro r hr
  rw [Finset.mem_singleton.1 hr]
  exact AddSubgroup.zero_mem _

private theorem existsUnique_mem_singleton_zero_of_mem_bot :
    ∀ x ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)),
      ∃! r, r ∈ ({0} : Finset (v.adicCompletion ℚ)) ∧ x - r ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)) := by
  intro x hx
  refine ⟨0, ⟨Finset.mem_singleton_self 0, by rwa [sub_zero]⟩, fun r hr => Finset.mem_singleton.1 hr.1⟩

private theorem isTransversal_upperUnipotentSubgroup {Bx By Bz Bx' By' Bz' : AddSubgroup (v.adicCompletion ℚ)}
    (h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz) (h' : ∀ x ∈ Bx', ∀ y ∈ By', x * y ∈ Bz') (hy : By' ≤ By)
    {X Y Z : Finset (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hX : ∀ r ∈ X, r ∈ Bx) (hX' : ∀ x ∈ Bx, ∃! r, r ∈ X ∧ x - r ∈ Bx')
    (hY : ∀ r ∈ Y, r ∈ By) (hY' : ∀ y ∈ By, ∃! r, r ∈ Y ∧ y - r ∈ By')
    (hZ : ∀ r ∈ Z, r ∈ Bz) (hZ' : ∀ z ∈ Bz, ∃! r, r ∈ Z ∧ z - r ∈ Bz')
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z) :
    IsTransversal (upperUnipotentSubgroup v Bx By Bz h) (upperUnipotentSubgroup v Bx' By' Bz' h') S := by
  refine ⟨fun s hs => ?_, fun k hk => ?_⟩
  · obtain ⟨x, hx, y, hy', z, hz, rfl⟩ := (hS s).1 hs
    exact mem_upperUnipotentSubgroup_iff.2 ⟨x, y, z, hX x hx, hY y hy', hZ z hz, rfl⟩
  · obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hk
    obtain ⟨rx, ⟨hrx, harx⟩, hux⟩ := hX' a ha
    obtain ⟨ry, ⟨hry, hbry⟩, huy⟩ := hY' b hb
    have ht : c - rx * (b - ry) ∈ Bz := Bz.sub_mem hc (h rx (hX rx hrx) (b - ry) (hy hbry))
    obtain ⟨rz, ⟨hrz, htrz⟩, huz⟩ := hZ' _ ht
    refine ⟨upperUnipotent3 rx ry rz, ⟨(hS _).2 ⟨rx, hrx, ry, hry, rz, hrz, rfl⟩,
      upperUnipotent3 (a - rx) (b - ry) (c - rx * (b - ry) - rz),
      mem_upperUnipotentSubgroup_iff.2 ⟨_, _, _, harx, hbry, htrz, rfl⟩, ?_⟩, ?_⟩
    · rw [BruhatCells.upperUnipotent3_mul_upperUnipotent3, show rx + (a - rx) = a by ring,
        show ry + (b - ry) = b by ring, show rz + (c - rx * (b - ry) - rz) + rx * (b - ry) = c by ring]
    · rintro s ⟨hs, κ, hκ, hk'⟩
      obtain ⟨rx', hrx', ry', hry', rz', hrz', rfl⟩ := (hS s).1 hs
      obtain ⟨a', b', c', ha', hb', hc', rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hκ
      rw [BruhatCells.upperUnipotent3_mul_upperUnipotent3, upperUnipotent3_eq_upperUnipotent3_iff] at hk'
      obtain ⟨hax, hby, hcz⟩ := hk'
      have erx : rx' = rx := hux rx' ⟨hrx', by rw [hax, add_sub_cancel_left]; exact ha'⟩
      have ery : ry' = ry := huy ry' ⟨hry', by rw [hby, add_sub_cancel_left]; exact hb'⟩
      have erz : rz' = rz := huz rz' ⟨hrz', by
        rw [show c - rx * (b - ry) - rz' = c' by rw [hcz, hby, ← erx, ← ery]; ring]
        exact hc'⟩
      rw [erx, ery, erz]

private theorem sum_eq_sum_upperUnipotent3 {X Y Z : Finset (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z) (φ : LocalGL3 v → ℂ) :
    ∑ s ∈ S, φ s = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, φ (upperUnipotent3 x y z) := by
  classical
  have hSe : S = (X ×ˢ Y ×ˢ Z).image
      (fun p => (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v)) := by
    ext g
    rw [hS g]
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, hx, y, hy', z, hz, rfl⟩
      exact ⟨x, y, z, ⟨hx, hy', hz⟩, rfl⟩
    · rintro ⟨x, y, z, ⟨hx, hy', hz⟩, rfl⟩
      exact ⟨x, hx, y, hy', z, hz, rfl⟩
  have hinj : Set.InjOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v)) ↑(X ×ˢ Y ×ˢ Z) := by
    rintro ⟨x, y, z⟩ - ⟨x', y', z'⟩ - hxyz
    have hxyz' : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 x' y' z' := hxyz
    obtain ⟨rfl, rfl, rfl⟩ := upperUnipotent3_eq_upperUnipotent3_iff.1 hxyz'
    rfl
  rw [hSe, Finset.sum_image hinj, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_product _ _ _

end UnipotentTransversal

end LanglandsTunnell.CubicInduction

end JoinPiece_Transversals

section JoinPiece_Spherical

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField NumberField.AdelicLevel Matrix

section SphericalSection

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def rightMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 1 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 1

private theorem rightMinor_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    rightMinor v (upperUnipotent3 x y z * g) = rightMinor v g := by
  simp only [rightMinor, gl3Entry_upperUnipotent3_mul_one, gl3Entry_upperUnipotent3_mul_two]
  ring

private theorem rightMinor_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    rightMinor v (diagonal3 v a * g) = ((a 1 : v.adicCompletion ℚ) * a 2) * rightMinor v g := by
  simp only [rightMinor, gl3Entry_diagonal3_mul]
  ring

private theorem continuous_rightMinor : Continuous (rightMinor v) :=
  ((continuous_gl3Entry v 1 1).mul (continuous_gl3Entry v 2 2)).sub
    ((continuous_gl3Entry v 1 2).mul (continuous_gl3Entry v 2 1))

private theorem gl3Det_eq_top_expansion (g : LocalGL3 v) :
    gl3Det v g = gl3Entry v g 0 0 * rightMinor v g - gl3Entry v g 0 1 * outerMinor v g
      + gl3Entry v g 0 2 * lowerMinor v g := by
  simp only [gl3Det, gl3Entry, rightMinor, outerMinor, lowerMinor, Matrix.det_fin_three]
  ring

private def bottomNorm (g : LocalGL3 v) : ℝ :=
  max (max ‖gl3Entry v g 2 0‖ ‖gl3Entry v g 2 1‖) ‖gl3Entry v g 2 2‖

private def minorNorm (g : LocalGL3 v) : ℝ :=
  max (max ‖lowerMinor v g‖ ‖outerMinor v g‖) ‖rightMinor v g‖

private theorem bottomNorm_pos (g : LocalGL3 v) : 0 < bottomNorm v g := by
  rw [bottomNorm]
  by_cases h0 : gl3Entry v g 2 0 = 0
  · rcases exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero v h0 with h1 | h2
    · exact lt_of_lt_of_le (norm_pos_iff.mpr h1) ((le_max_right _ _).trans (le_max_left _ _))
    · exact lt_of_lt_of_le (norm_pos_iff.mpr h2) (le_max_right _ _)
  · exact lt_of_lt_of_le (norm_pos_iff.mpr h0) ((le_max_left _ _).trans (le_max_left _ _))

private theorem minorNorm_pos (g : LocalGL3 v) : 0 < minorNorm v g := by
  rw [minorNorm]
  by_cases hl : lowerMinor v g = 0
  · by_cases ho : outerMinor v g = 0
    · have hr : rightMinor v g ≠ 0 := by
        intro hr
        apply gl3Det_ne_zero v g
        rw [gl3Det_eq_top_expansion, hl, ho, hr]
        ring
      exact lt_of_lt_of_le (norm_pos_iff.mpr hr) (le_max_right _ _)
    · exact lt_of_lt_of_le (norm_pos_iff.mpr ho) ((le_max_right _ _).trans (le_max_left _ _))
  · exact lt_of_lt_of_le (norm_pos_iff.mpr hl) ((le_max_left _ _).trans (le_max_left _ _))

private theorem eventually_max_norm_eq {e₁ e₂ e₃ : LocalGL3 v → v.adicCompletion ℚ} (h₁ : Continuous e₁)
    (h₂ : Continuous e₂) (h₃ : Continuous e₃) (p : LocalGL3 v) {m : ℝ}
    (hm : max (max ‖e₁ p‖ ‖e₂ p‖) ‖e₃ p‖ = m) (hpos : 0 < m) :
    ∀ᶠ g in nhds p, max (max ‖e₁ g‖ ‖e₂ g‖) ‖e₃ g‖ = m := by
  have key : ∀ {e : LocalGL3 v → v.adicCompletion ℚ}, Continuous e → ‖e p‖ ≤ m →
      ∀ᶠ g in nhds p, ‖e g‖ ≤ m := by
    intro e he hle
    rcases hle.lt_or_eq with hlt | heq
    · exact (he.norm.tendsto p).eventually_le_const hlt
    · have hne : e p ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at heq
        exact hpos.ne heq
      filter_upwards [(he.tendsto p).eventually (eventually_norm_eq v hne)] with g hg
      rw [hg]
      exact heq.le
  have att : ∀ {e : LocalGL3 v → v.adicCompletion ℚ}, Continuous e → ‖e p‖ = m →
      ∀ᶠ g in nhds p, ‖e g‖ = m := by
    intro e he heq
    have hne : e p ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at heq
      exact hpos.ne heq
    filter_upwards [(he.tendsto p).eventually (eventually_norm_eq v hne)] with g hg
    rw [hg]
    exact heq
  have le₁ : ‖e₁ p‖ ≤ m := by
    rw [← hm]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have le₂ : ‖e₂ p‖ ≤ m := by
    rw [← hm]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have le₃ : ‖e₃ p‖ ≤ m := by
    rw [← hm]
    exact le_max_right _ _
  have hge : ∀ᶠ g in nhds p, m ≤ max (max ‖e₁ g‖ ‖e₂ g‖) ‖e₃ g‖ := by
    rcases le_total (max ‖e₁ p‖ ‖e₂ p‖) ‖e₃ p‖ with h3 | h3
    · rw [max_eq_right h3] at hm
      filter_upwards [att h₃ hm] with g hg
      rw [← hg]
      exact le_max_right _ _
    · rw [max_eq_left h3] at hm
      rcases le_total ‖e₁ p‖ ‖e₂ p‖ with h12 | h12
      · rw [max_eq_right h12] at hm
        filter_upwards [att h₂ hm] with g hg
        rw [← hg]
        exact (le_max_right _ _).trans (le_max_left _ _)
      · rw [max_eq_left h12] at hm
        filter_upwards [att h₁ hm] with g hg
        rw [← hg]
        exact (le_max_left _ _).trans (le_max_left _ _)
  filter_upwards [key h₁ le₁, key h₂ le₂, key h₃ le₃, hge] with g hg₁ hg₂ hg₃ hg
  exact le_antisymm (max_le (max_le hg₁ hg₂) hg₃) hg

private def sphericalSection3 (g : LocalGL3 v) : ℂ :=
  ((‖gl3Det v g‖ / (minorNorm v g * bottomNorm v g) : ℝ) : ℂ)

private theorem sphericalSection3_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    sphericalSection3 v (upperUnipotent3 x y z * g) = sphericalSection3 v g := by
  simp only [sphericalSection3, minorNorm, bottomNorm, gl3Det_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul,
    outerMinor_upperUnipotent3_mul, rightMinor_upperUnipotent3_mul, gl3Entry_upperUnipotent3_mul_two]

private theorem torusChar3_trivial (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : torusChar3 v (fun _ => 1) a = 1 := by
  simp [torusChar3]

private theorem ne_zero_halfModulus3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : halfModulus3 v a ≠ 0 := by
  unfold halfModulus3
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero (norm_ne_zero_iff.mpr (a 0).ne_zero) (norm_ne_zero_iff.mpr (a 2).ne_zero))

private theorem sphericalSection3_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    sphericalSection3 v (diagonal3 v a * g) =
      torusChar3 v (fun _ => 1) a * halfModulus3 v a * sphericalSection3 v g := by
  have h1 : (0 : ℝ) < ‖(a 1 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (a 1).ne_zero
  have h2 : (0 : ℝ) < ‖(a 2 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (a 2).ne_zero
  have h12 : (0 : ℝ) ≤ ‖(a 1 : v.adicCompletion ℚ)‖ * ‖(a 2 : v.adicCompletion ℚ)‖ := (mul_pos h1 h2).le
  have hM : minorNorm v (diagonal3 v a * g) =
      ‖(a 1 : v.adicCompletion ℚ)‖ * ‖(a 2 : v.adicCompletion ℚ)‖ * minorNorm v g := by
    simp only [minorNorm, lowerMinor_diagonal3_mul, outerMinor_diagonal3_mul, rightMinor_diagonal3_mul, norm_mul,
      mul_max_of_nonneg _ _ h12]
  have hB : bottomNorm v (diagonal3 v a * g) = ‖(a 2 : v.adicCompletion ℚ)‖ * bottomNorm v g := by
    simp only [bottomNorm, gl3Entry_diagonal3_mul, norm_mul,
      mul_max_of_nonneg _ _ (norm_nonneg (a 2 : v.adicCompletion ℚ))]
  have hMg : minorNorm v g ≠ 0 := (minorNorm_pos v g).ne'
  have hBg : bottomNorm v g ≠ 0 := (bottomNorm_pos v g).ne'
  rw [sphericalSection3, sphericalSection3, hM, hB, gl3Det_diagonal3_mul, torusChar3_trivial, one_mul, halfModulus3,
    ← Complex.ofReal_mul, Complex.ofReal_inj, norm_mul, norm_mul, norm_mul, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero h1.ne' h2.ne') hMg) (mul_ne_zero h2.ne' hBg))
      (mul_ne_zero h2.ne' (mul_ne_zero hMg hBg))]
  ring

private theorem isLocallyConstant_sphericalSection3 : IsLocallyConstant (sphericalSection3 v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hdet : ∀ᶠ h in nhds g, ‖gl3Det v h‖ = ‖gl3Det v g‖ :=
    ((continuous_gl3Det v).tendsto g).eventually (eventually_norm_eq v (gl3Det_ne_zero v g))
  have hM : ∀ᶠ h in nhds g, minorNorm v h = minorNorm v g :=
    eventually_max_norm_eq v (continuous_lowerMinor v) (continuous_outerMinor v) (continuous_rightMinor v) g rfl
      (minorNorm_pos v g)
  have hB : ∀ᶠ h in nhds g, bottomNorm v h = bottomNorm v g :=
    eventually_max_norm_eq v (continuous_gl3Entry v 2 0) (continuous_gl3Entry v 2 1) (continuous_gl3Entry v 2 2) g
      rfl (bottomNorm_pos v g)
  filter_upwards [hdet, hM, hB] with h hd hm hb
  simp only [sphericalSection3, hd, hm, hb]

private theorem sphericalSection3_mem : sphericalSection3 v ∈ principalSeries3 v (fun _ => 1) :=
  ⟨isLocallyConstant_sphericalSection3 v, sphericalSection3_upperUnipotent3_mul v, sphericalSection3_diagonal3_mul v⟩

private def sphericalVector : ↥(principalSeries3 v (fun _ => 1)) := ⟨sphericalSection3 v, sphericalSection3_mem v⟩

private def translateVector (g : LocalGL3 v) (f : ↥(principalSeries3 v (fun _ => 1))) :
    ↥(principalSeries3 v (fun _ => 1)) :=
  ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩

private theorem translateVector_apply (g : LocalGL3 v) (f : ↥(principalSeries3 v (fun _ => 1))) (h : LocalGL3 v) :
    (translateVector v g f : LocalGL3 v → ℂ) h = (f : LocalGL3 v → ℂ) (h * g) :=
  rfl

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

private theorem norm_uniformizerUnit :
    ‖(uniformizerUnit ℚ v : v.adicCompletion ℚ)‖ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp]
  simp

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h := one_lt_natCard_quot v
  rw [natCard_quot_eq_absNorm] at h
  exact_mod_cast h

private theorem absNorm_real_ne_zero : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
  (zero_lt_one.trans (one_lt_absNorm_real v)).ne'

private theorem norm_uniformizerUnit_inv :
    ‖(((uniformizerUnit ℚ v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [Units.val_inv_eq_inv_val, norm_inv, norm_uniformizerUnit, inv_inv]

private theorem halfModulus3_left (u : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![u, 1, 1] = ((‖(u : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem halfModulus3_middle (u : (v.adicCompletion ℚ)ˣ) : halfModulus3 v ![1, u, 1] = 1 := by
  simp [halfModulus3]

private theorem halfModulus3_right (u : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![1, 1, u] = ((‖(u : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem absNorm_cancel (c : ℂ) :
    c - ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) * (1 * (((Ideal.absNorm v.asIdeal : ℝ)⁻¹ : ℝ) : ℂ) * c) = 0 := by
  rw [one_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (absNorm_real_ne_zero v), Complex.ofReal_one,
    one_mul, sub_self]

private def cellRep1 (x : v.adicCompletion ℚ) : LocalGL3 v where
  val := !![0, 1, 0; 1, x, 0; 0, 0, 1]
  inv := !![-x, 1, 0; 1, 0, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem cellRep1_coe (x : v.adicCompletion ℚ) :
    (cellRep1 v x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![0, 1, 0; 1, x, 0; 0, 0, 1] :=
  rfl

private def cellRep2 (y : v.adicCompletion ℚ) : LocalGL3 v where
  val := !![1, 0, 0; 0, 0, 1; 0, 1, y]
  inv := !![1, 0, 0; 0, -y, 1; 0, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem cellRep2_coe (y : v.adicCompletion ℚ) :
    (cellRep2 v y : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![1, 0, 0; 0, 0, 1; 0, 1, y] :=
  rfl

private def lowerUnipotent10 (w : v.adicCompletion ℚ) : LocalGL3 v where
  val := !![1, 0, 0; w, 1, 0; 0, 0, 1]
  inv := !![1, 0, 0; -w, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerUnipotent10_coe (w : v.adicCompletion ℚ) :
    (lowerUnipotent10 v w : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![1, 0, 0; w, 1, 0; 0, 0, 1] :=
  rfl

private def lowerUnipotent21 (w : v.adicCompletion ℚ) : LocalGL3 v where
  val := !![1, 0, 0; 0, 1, 0; 0, w, 1]
  inv := !![1, 0, 0; 0, 1, 0; 0, -w, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerUnipotent21_coe (w : v.adicCompletion ℚ) :
    (lowerUnipotent21 v w : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![1, 0, 0; 0, 1, 0; 0, w, 1] :=
  rfl

private theorem lowerUnipotent10_zero : lowerUnipotent10 v 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent10_coe]

private theorem lowerUnipotent21_zero : lowerUnipotent21 v 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent21_coe]

private theorem continuous_cellRep1 : Continuous (cellRep1 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : v.adicCompletion ℚ => !![(0 : v.adicCompletion ℚ), 1, 0; 1, x, 0; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : v.adicCompletion ℚ => !![-x, (1 : v.adicCompletion ℚ), 0; 1, 0, 0; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_cellRep2 : Continuous (cellRep2 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun y : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; 0, 0, 1; 0, 1, y]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun y : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; 0, -y, 1; 0, 1, 0]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_lowerUnipotent10 : Continuous (lowerUnipotent10 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun w : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; w, 1, 0; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun w : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; -w, 1, 0; 0, 0, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_lowerUnipotent21 : Continuous (lowerUnipotent21 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun w : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; 0, 1, 0; 0, w, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun w : v.adicCompletion ℚ => !![(1 : v.adicCompletion ℚ), 0, 0; 0, 1, 0; 0, -w, 1]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem cellRep1_mul_upperUnipotent3 (x u : v.adicCompletion ℚ) :
    cellRep1 v x * upperUnipotent3 u 0 0 = cellRep1 v (x + u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep1_coe, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

private theorem cellRep2_mul_upperUnipotent3 (y u : v.adicCompletion ℚ) :
    cellRep2 v y * upperUnipotent3 0 u 0 = cellRep2 v (y + u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep2_coe, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

private theorem cellRep1_mul_diagonal3 (x : v.adicCompletion ℚ) (u : (v.adicCompletion ℚ)ˣ) :
    cellRep1 v x * diagonal3 v ![1, u, 1] = diagonal3 v ![u, 1, 1] * cellRep1 v ((u : v.adicCompletion ℚ) * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep1_coe, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

private theorem cellRep1_mul_diagonal3_right (x : v.adicCompletion ℚ) (u : (v.adicCompletion ℚ)ˣ) :
    cellRep1 v x * diagonal3 v ![1, 1, u] = diagonal3 v ![1, 1, u] * cellRep1 v x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep1_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem cellRep2_mul_diagonal3_left (y : v.adicCompletion ℚ) (u : (v.adicCompletion ℚ)ˣ) :
    cellRep2 v y * diagonal3 v ![u, 1, 1] = diagonal3 v ![u, 1, 1] * cellRep2 v y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep2_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem cellRep2_mul_diagonal3 (y : v.adicCompletion ℚ) (u : (v.adicCompletion ℚ)ˣ) :
    cellRep2 v y * diagonal3 v ![1, 1, u] = diagonal3 v ![1, u, 1] * cellRep2 v ((u : v.adicCompletion ℚ) * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep2_coe, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

private theorem cellRep1_eq_of_ne_zero {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    cellRep1 v x = diagonal3 v ![Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx)), Units.mk0 x hx, 1] *
      (upperUnipotent3 (-x) 0 0 * lowerUnipotent10 v x⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cellRep1_coe, lowerUnipotent10_coe, Matrix.mul_apply, Fin.sum_univ_three, hx]

private theorem cellRep2_eq_of_ne_zero {y : v.adicCompletion ℚ} (hy : y ≠ 0) :
    cellRep2 v y = diagonal3 v ![1, Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)), Units.mk0 y hy] *
      (upperUnipotent3 0 (-y) 0 * lowerUnipotent21 v y⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cellRep2_coe, lowerUnipotent21_coe, Matrix.mul_apply, Fin.sum_univ_three, hy]

private theorem exists_eq_mul_cellRep1 (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h21 : gl3Entry v g 2 1 = 0)
    (h10 : gl3Entry v g 1 0 ≠ 0) :
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (w : v.adicCompletion ℚ),
      g = upperUnipotent3 x y z * (diagonal3 v a * cellRep1 v w) := by
  have h20' : g.val 2 0 = 0 := h20
  have h21' : g.val 2 1 = 0 := h21
  have h10' : g.val 1 0 ≠ 0 := h10
  have hdet : g.val.det ≠ 0 := gl3Det_ne_zero v g
  have hexp : g.val.det = g.val 2 2 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) := by
    rw [Matrix.det_fin_three, h20', h21']
    ring
  rw [hexp] at hdet
  obtain ⟨h22, hm⟩ := mul_ne_zero_iff.1 hdet
  refine ⟨g.val 0 0 / g.val 1 0, g.val 1 2 / g.val 2 2, g.val 0 2 / g.val 2 2,
    ![Units.mk0 (-(g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) / g.val 1 0)
        (div_ne_zero (neg_ne_zero.mpr hm) h10'),
      Units.mk0 (g.val 1 0) h10', Units.mk0 (g.val 2 2) h22], g.val 1 1 / g.val 1 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep1_coe, Matrix.mul_apply, Fin.sum_univ_three, h20', h21', h10', h22]
  all_goals field_simp
  all_goals ring

private theorem exists_eq_mul_cellRep2 (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0)
    (h21 : gl3Entry v g 2 1 ≠ 0) :
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (w : v.adicCompletion ℚ),
      g = upperUnipotent3 x y z * (diagonal3 v a * cellRep2 v w) := by
  have h20' : g.val 2 0 = 0 := h20
  have h10' : g.val 1 0 = 0 := h10
  have h21' : g.val 2 1 ≠ 0 := h21
  have hdet : g.val.det ≠ 0 := gl3Det_ne_zero v g
  have hexp : g.val.det = g.val 0 0 * (g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1) := by
    rw [Matrix.det_fin_three, h20', h10']
    ring
  rw [hexp] at hdet
  obtain ⟨h00, hr⟩ := mul_ne_zero_iff.1 hdet
  obtain ⟨r, hr_def⟩ : ∃ r : v.adicCompletion ℚ, r = g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1 := ⟨_, rfl⟩
  rw [← hr_def] at hr
  refine ⟨(g.val 0 1 * g.val 2 2 - g.val 0 2 * g.val 2 1) / r, g.val 1 1 / g.val 2 1, g.val 0 1 / g.val 2 1,
    ![Units.mk0 (g.val 0 0) h00, Units.mk0 (-r / g.val 2 1) (div_ne_zero (neg_ne_zero.mpr hr) h21'),
      Units.mk0 (g.val 2 1) h21'], g.val 2 2 / g.val 2 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep2_coe, Matrix.mul_apply, Fin.sum_univ_three, h20', h10', h21']
  all_goals field_simp
  all_goals subst hr_def
  all_goals ring

private theorem gl3Entry_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (i j : Fin 3) :
    gl3Entry v (g * diagonal3 v a) i j = gl3Entry v g i j * (a j : v.adicCompletion ℚ) := by
  simp [gl3Entry, diagonal3_coe, Matrix.mul_diagonal]

private theorem gl3Entry_mul_upperUnipotent3_two_zero (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    gl3Entry v (g * upperUnipotent3 x y z) 2 0 = gl3Entry v g 2 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem entry_one_zero_mul_upperUnipotent3 (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    gl3Entry v (g * upperUnipotent3 x y z) 1 0 = gl3Entry v g 1 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem entry_two_one_mul_upperUnipotent3 (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) :
    gl3Entry v (g * upperUnipotent3 x y z) 2 1 = gl3Entry v g 2 0 * x + gl3Entry v g 2 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sub_inv_halfModulus3_mul_apply_mul_diagonal3_right {h : LocalGL3 v → ℂ}
    (hh : h ∈ principalSeries3 v (fun _ => 1)) (u : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h21 : gl3Entry v g 2 1 = 0) :
    h g - (halfModulus3 v ![1, 1, u])⁻¹ * h (g * diagonal3 v ![1, 1, u]) = 0 := by
  have hΔ : (h - (halfModulus3 v ![1, 1, u])⁻¹ • gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, u]) h) ∈
      principalSeries3 v (fun _ => 1) :=
    (principalSeries3 v (fun _ => 1)).sub_mem hh
      ((principalSeries3 v (fun _ => 1)).smul_mem _ (rightTranslate_mem_principalSeries3 hh (diagonal3 v ![1, 1, u])))
  have hkey : ∀ g' : LocalGL3 v, g' * diagonal3 v ![1, 1, u] = diagonal3 v ![1, 1, u] * g' →
      (h - (halfModulus3 v ![1, 1, u])⁻¹ • gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, u]) h) g' = 0 := by
    intro g' hg'
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply]
    rw [hg', apply_diagonal3_mul_of_mem_principalSeries3 hh, torusChar3_trivial, one_mul, ← mul_assoc,
      inv_mul_cancel₀ (ne_zero_halfModulus3 v _), one_mul, sub_self]
  have hval :
      (h - (halfModulus3 v ![1, 1, u])⁻¹ • gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, u]) h) g = 0 := by
    by_cases h10 : gl3Entry v g 1 0 = 0
    · exact apply_eq_zero_of_apply_one_eq_zero v hΔ (hkey 1 (by rw [one_mul, mul_one])) g h20 h10 h21
    · obtain ⟨_, _, _, _, w, hg⟩ := exists_eq_mul_cellRep1 v g h20 h21 h10
      rw [hg, apply_upperUnipotent3_mul_of_mem_principalSeries3 hΔ, apply_diagonal3_mul_of_mem_principalSeries3 hΔ,
        hkey _ (cellRep1_mul_diagonal3_right v w u), mul_zero]
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply] using hval

private theorem sub_inv_halfModulus3_mul_apply_mul_diagonal3_left {h : LocalGL3 v → ℂ}
    (hh : h ∈ principalSeries3 v (fun _ => 1)) (u : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0) :
    h g - (halfModulus3 v ![u, 1, 1])⁻¹ * h (g * diagonal3 v ![u, 1, 1]) = 0 := by
  have hΔ : (h - (halfModulus3 v ![u, 1, 1])⁻¹ • gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![u, 1, 1]) h) ∈
      principalSeries3 v (fun _ => 1) :=
    (principalSeries3 v (fun _ => 1)).sub_mem hh
      ((principalSeries3 v (fun _ => 1)).smul_mem _ (rightTranslate_mem_principalSeries3 hh (diagonal3 v ![u, 1, 1])))
  have hkey : ∀ g' : LocalGL3 v, g' * diagonal3 v ![u, 1, 1] = diagonal3 v ![u, 1, 1] * g' →
      (h - (halfModulus3 v ![u, 1, 1])⁻¹ • gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![u, 1, 1]) h) g' = 0 := by
    intro g' hg'
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply]
    rw [hg', apply_diagonal3_mul_of_mem_principalSeries3 hh, torusChar3_trivial, one_mul, ← mul_assoc,
      inv_mul_cancel₀ (ne_zero_halfModulus3 v _), one_mul, sub_self]
  have hval :
      (h - (halfModulus3 v ![u, 1, 1])⁻¹ • gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![u, 1, 1]) h) g = 0 := by
    by_cases h21 : gl3Entry v g 2 1 = 0
    · exact apply_eq_zero_of_apply_one_eq_zero v hΔ (hkey 1 (by rw [one_mul, mul_one])) g h20 h10 h21
    · obtain ⟨_, _, _, _, w, hg⟩ := exists_eq_mul_cellRep2 v g h20 h10 h21
      rw [hg, apply_upperUnipotent3_mul_of_mem_principalSeries3 hΔ, apply_diagonal3_mul_of_mem_principalSeries3 hΔ,
        hkey _ (cellRep2_mul_diagonal3_left v w u), mul_zero]
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply] using hval

private def profile1 : (LocalGL3 v → ℂ) →ₗ[ℂ] (v.adicCompletion ℚ → ℂ) := LinearMap.funLeft ℂ ℂ (cellRep1 v)

private def profile2 : (LocalGL3 v → ℂ) →ₗ[ℂ] (v.adicCompletion ℚ → ℂ) := LinearMap.funLeft ℂ ℂ (cellRep2 v)

private theorem profile1_apply (f : LocalGL3 v → ℂ) (x : v.adicCompletion ℚ) : profile1 v f x = f (cellRep1 v x) :=
  rfl

private theorem profile2_apply (f : LocalGL3 v → ℂ) (y : v.adicCompletion ℚ) : profile2 v f y = f (cellRep2 v y) :=
  rfl

private theorem profile1_mem_stepFunctions {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v (fun _ => 1))
    (h1 : f 1 = 0) : profile1 v f ∈ stepFunctions v := by
  refine (mem_stepFunctions_iff v _).mpr ⟨?_, ?_⟩
  · exact (isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous (continuous_cellRep1 v)
  · have hU : IsOpen {w : v.adicCompletion ℚ | f (lowerUnipotent10 v w) = 0} :=
      ((isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous (continuous_lowerUnipotent10 v)).isOpen_fiber 0
    have h0 : (0 : v.adicCompletion ℚ) ∈ {w : v.adicCompletion ℚ | f (lowerUnipotent10 v w) = 0} := by
      show f (lowerUnipotent10 v 0) = 0
      rw [lowerUnipotent10_zero, h1]
    obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen v hU h0
    refine HasCompactSupport.intro (isCompact_setOf_valued_sub_le v 0 (-j)) fun x hx => ?_
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hx
      show Valued.v ((0 : v.adicCompletion ℚ) - 0) ≤ WithZero.exp (-(-j))
      rw [sub_zero, map_zero]
      exact zero_le'
    have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    have hxm : Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log hvx).symm
    have hjm : ¬ WithZero.log (Valued.v x) ≤ -(-j) := by
      intro hle
      apply hx
      show Valued.v (x - 0) ≤ WithZero.exp (-(-j))
      rw [sub_zero, hxm]
      exact WithZero.exp_le_exp.mpr hle
    have hmem : x⁻¹ ∈ {w : v.adicCompletion ℚ | Valued.v (w - 0) ≤ WithZero.exp (-j)} := by
      show Valued.v (x⁻¹ - 0) ≤ WithZero.exp (-j)
      rw [sub_zero, map_inv₀, hxm, ← WithZero.exp_neg]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hl : f (lowerUnipotent10 v x⁻¹) = 0 := by
      have h := hj hmem
      exact h
    show f (cellRep1 v x) = 0
    rw [cellRep1_eq_of_ne_zero v hx0, apply_diagonal3_mul_of_mem_principalSeries3 hf,
      apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, hl, mul_zero]

private theorem profile2_mem_stepFunctions {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v (fun _ => 1))
    (h1 : f 1 = 0) : profile2 v f ∈ stepFunctions v := by
  refine (mem_stepFunctions_iff v _).mpr ⟨?_, ?_⟩
  · exact (isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous (continuous_cellRep2 v)
  · have hU : IsOpen {w : v.adicCompletion ℚ | f (lowerUnipotent21 v w) = 0} :=
      ((isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous (continuous_lowerUnipotent21 v)).isOpen_fiber 0
    have h0 : (0 : v.adicCompletion ℚ) ∈ {w : v.adicCompletion ℚ | f (lowerUnipotent21 v w) = 0} := by
      show f (lowerUnipotent21 v 0) = 0
      rw [lowerUnipotent21_zero, h1]
    obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen v hU h0
    refine HasCompactSupport.intro (isCompact_setOf_valued_sub_le v 0 (-j)) fun y hy => ?_
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hy
      show Valued.v ((0 : v.adicCompletion ℚ) - 0) ≤ WithZero.exp (-(-j))
      rw [sub_zero, map_zero]
      exact zero_le'
    have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    have hym : Valued.v y = WithZero.exp (WithZero.log (Valued.v y)) := (WithZero.exp_log hvy).symm
    have hjm : ¬ WithZero.log (Valued.v y) ≤ -(-j) := by
      intro hle
      apply hy
      show Valued.v (y - 0) ≤ WithZero.exp (-(-j))
      rw [sub_zero, hym]
      exact WithZero.exp_le_exp.mpr hle
    have hmem : y⁻¹ ∈ {w : v.adicCompletion ℚ | Valued.v (w - 0) ≤ WithZero.exp (-j)} := by
      show Valued.v (y⁻¹ - 0) ≤ WithZero.exp (-j)
      rw [sub_zero, map_inv₀, hym, ← WithZero.exp_neg]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hl : f (lowerUnipotent21 v y⁻¹) = 0 := by
      have h := hj hmem
      exact h
    show f (cellRep2 v y) = 0
    rw [cellRep2_eq_of_ne_zero v hy0, apply_diagonal3_mul_of_mem_principalSeries3 hf,
      apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, hl, mul_zero]

private theorem sphericalSection3_cellRep1 (x : v.adicCompletion ℚ) :
    sphericalSection3 v (cellRep1 v x) = (((max 1 ‖x‖)⁻¹ : ℝ) : ℂ) := by
  have hdet : gl3Det v (cellRep1 v x) = -1 := by simp [gl3Det, cellRep1_coe, Matrix.det_fin_three]
  have hl : lowerMinor v (cellRep1 v x) = 0 := by simp [lowerMinor, gl3Entry, cellRep1_coe]
  have ho : outerMinor v (cellRep1 v x) = 1 := by simp [outerMinor, gl3Entry, cellRep1_coe]
  have hr : rightMinor v (cellRep1 v x) = x := by simp [rightMinor, gl3Entry, cellRep1_coe]
  have h20 : gl3Entry v (cellRep1 v x) 2 0 = 0 := by simp [gl3Entry, cellRep1_coe]
  have h21 : gl3Entry v (cellRep1 v x) 2 1 = 0 := by simp [gl3Entry, cellRep1_coe]
  have h22 : gl3Entry v (cellRep1 v x) 2 2 = 1 := by simp [gl3Entry, cellRep1_coe]
  have hM : minorNorm v (cellRep1 v x) = max 1 ‖x‖ := by
    rw [minorNorm, hl, ho, hr, norm_zero, norm_one, max_eq_right (zero_le_one' ℝ)]
  have hB : bottomNorm v (cellRep1 v x) = 1 := by
    rw [bottomNorm, h20, h21, h22, norm_zero, norm_one, max_self, max_eq_right (zero_le_one' ℝ)]
  rw [sphericalSection3, hdet, hM, hB, norm_neg, norm_one, mul_one, one_div]

private theorem sphericalSection3_cellRep2 (y : v.adicCompletion ℚ) :
    sphericalSection3 v (cellRep2 v y) = (((max 1 ‖y‖)⁻¹ : ℝ) : ℂ) := by
  have hdet : gl3Det v (cellRep2 v y) = -1 := by simp [gl3Det, cellRep2_coe, Matrix.det_fin_three]
  have hl : lowerMinor v (cellRep2 v y) = 0 := by simp [lowerMinor, gl3Entry, cellRep2_coe]
  have ho : outerMinor v (cellRep2 v y) = 0 := by simp [outerMinor, gl3Entry, cellRep2_coe]
  have hr : rightMinor v (cellRep2 v y) = -1 := by simp [rightMinor, gl3Entry, cellRep2_coe]
  have h20 : gl3Entry v (cellRep2 v y) 2 0 = 0 := by simp [gl3Entry, cellRep2_coe]
  have h21 : gl3Entry v (cellRep2 v y) 2 1 = 1 := by simp [gl3Entry, cellRep2_coe]
  have h22 : gl3Entry v (cellRep2 v y) 2 2 = y := by simp [gl3Entry, cellRep2_coe]
  have hM : minorNorm v (cellRep2 v y) = 1 := by
    rw [minorNorm, hl, ho, hr, norm_zero, norm_neg, norm_one, max_self, max_eq_right (zero_le_one' ℝ)]
  have hB : bottomNorm v (cellRep2 v y) = max 1 ‖y‖ := by
    rw [bottomNorm, h20, h21, h22, norm_zero, norm_one, max_eq_right (zero_le_one' ℝ)]
  rw [sphericalSection3, hdet, hM, hB, norm_neg, norm_one, one_mul, one_div]

private theorem ball_identity (x : v.adicCompletion ℚ) :
    (((max 1 ‖x‖)⁻¹ : ℝ) : ℂ) -
        ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) * (((max 1 ((Ideal.absNorm v.asIdeal : ℝ) * ‖x‖))⁻¹ : ℝ) : ℂ) =
      (1 - (Ideal.absNorm v.asIdeal : ℂ)) * ballIndicator v 0 1 x := by
  have hq := one_lt_absNorm_real v
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hq
  simp only [ballIndicator, sub_zero]
  split_ifs with hx
  · have hxp : ‖x‖ ≤ ‖(uniformizerUnit ℚ v : v.adicCompletion ℚ)‖ :=
      Valued.toNormedField.norm_le_iff.mpr (by rw [valued_uniformizerUnit]; exact hx)
    rw [norm_uniformizerUnit] at hxp
    have hx1 : ‖x‖ ≤ 1 := hxp.trans (inv_le_one_of_one_le₀ hq.le)
    have hnx : (Ideal.absNorm v.asIdeal : ℝ) * ‖x‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hxp hq0.le
      rwa [mul_inv_cancel₀ hq0.ne'] at h
    rw [max_eq_left hx1, max_eq_left hnx]
    simp
  · have h1x : (1 : ℝ) ≤ ‖x‖ := by
      have hv : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v x := by
        by_contra hlt
        exact hx ((withZero_lt_one_iff_le_exp_neg_one _).mp (not_le.mp hlt))
      have h : ‖(1 : v.adicCompletion ℚ)‖ ≤ ‖x‖ :=
        Valued.toNormedField.norm_le_iff.mpr (by rw [map_one]; exact hv)
      rwa [norm_one] at h
    have hnx : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) * ‖x‖ := one_le_mul_of_one_le_of_one_le hq.le h1x
    rw [max_eq_right h1x, max_eq_right hnx, _root_.mul_inv, ← Complex.ofReal_mul, mul_inv_cancel_left₀ hq0.ne',
      sub_self, mul_zero]

private theorem cellRep1_mul_diagonal3_left (x : v.adicCompletion ℚ) (u : (v.adicCompletion ℚ)ˣ) :
    cellRep1 v x * diagonal3 v ![u, 1, 1] =
      diagonal3 v ![1, u, 1] * cellRep1 v (((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellRep1_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem cellRep1_eq_cellRep1_zero_mul (x : v.adicCompletion ℚ) :
    cellRep1 v x = cellRep1 v 0 * upperUnipotent3 x 0 0 := by
  rw [cellRep1_mul_upperUnipotent3, zero_add]

private theorem cellRep2_eq_cellRep2_zero_mul (y : v.adicCompletion ℚ) :
    cellRep2 v y = cellRep2 v 0 * upperUnipotent3 0 y 0 := by
  rw [cellRep2_mul_upperUnipotent3, zero_add]

private def uniformizerDifference (h : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  h - (halfModulus3 v ![uniformizerUnit ℚ v, 1, 1])⁻¹ •
    gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![uniformizerUnit ℚ v, 1, 1]) h

private theorem uniformizerDifference_apply (h : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    uniformizerDifference v h g =
      h g - (halfModulus3 v ![uniformizerUnit ℚ v, 1, 1])⁻¹ * h (g * diagonal3 v ![uniformizerUnit ℚ v, 1, 1]) := by
  unfold uniformizerDifference
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply]

private theorem uniformizerDifference_mem {h : LocalGL3 v → ℂ} (hh : h ∈ principalSeries3 v (fun _ => 1)) :
    uniformizerDifference v h ∈ principalSeries3 v (fun _ => 1) := by
  unfold uniformizerDifference
  exact (principalSeries3 v (fun _ => 1)).sub_mem hh
    ((principalSeries3 v (fun _ => 1)).smul_mem _
      (rightTranslate_mem_principalSeries3 hh (diagonal3 v ![uniformizerUnit ℚ v, 1, 1])))

private theorem uniformizerDifference_cellRep1 {h : LocalGL3 v → ℂ} (hh : h ∈ principalSeries3 v (fun _ => 1))
    (x : v.adicCompletion ℚ) :
    uniformizerDifference v h (cellRep1 v x) =
      h (cellRep1 v x) -
        ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
          h (cellRep1 v ((((uniformizerUnit ℚ v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x)) := by
  rw [uniformizerDifference_apply, halfModulus3_left, norm_uniformizerUnit, Complex.ofReal_inv, inv_inv,
    cellRep1_mul_diagonal3_left, apply_diagonal3_mul_of_mem_principalSeries3 hh, torusChar3_trivial,
    halfModulus3_middle, one_mul, one_mul]

private theorem uniformizerDifference_sphericalSection3_cellRep1 (x : v.adicCompletion ℚ) :
    uniformizerDifference v (sphericalSection3 v) (cellRep1 v x) =
      (1 - (Ideal.absNorm v.asIdeal : ℂ)) * ballIndicator v 0 1 x := by
  rw [uniformizerDifference_cellRep1 v (sphericalSection3_mem v), sphericalSection3_cellRep1,
    sphericalSection3_cellRep1, norm_mul, norm_uniformizerUnit_inv]
  exact ball_identity v x

private theorem uniformizerDifference_uniformizerDifference_sphericalSection3_cellRep1 (x : v.adicCompletion ℚ) :
    uniformizerDifference v (uniformizerDifference v (sphericalSection3 v)) (cellRep1 v x) =
      (1 - (Ideal.absNorm v.asIdeal : ℂ)) *
        (ballIndicator v 0 1 x - (Ideal.absNorm v.asIdeal : ℂ) * ballIndicator v 0 2 x) := by
  have ht : ((((uniformizerUnit ℚ v)⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) ≠ 0 := Units.ne_zero _
  have htv : Valued.v ((((uniformizerUnit ℚ v)⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) =
      WithZero.exp (-(-1 : ℤ)) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit]
    simp
  have hb : ballIndicator v 0 1 ((((uniformizerUnit ℚ v)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) =
      ballIndicator v 0 2 x := by
    have h := congr_fun (ballIndicator_comp_mul_left v ht htv 0 1) x
    simp only [mul_zero] at h
    rw [h]
    norm_num
  rw [uniformizerDifference_cellRep1 v (uniformizerDifference_mem v (sphericalSection3_mem v)),
    uniformizerDifference_sphericalSection3_cellRep1, uniformizerDifference_sphericalSection3_cellRep1, hb,
    Complex.ofReal_natCast]
  ring

private def witness1 : ↥(principalSeries3 v (fun _ => 1)) :=
  sphericalVector v - translateVector v (diagonal3 v ![1, (uniformizerUnit ℚ v)⁻¹, 1]) (sphericalVector v)

private theorem witness1_apply (g : LocalGL3 v) :
    (witness1 v : LocalGL3 v → ℂ) g =
      sphericalSection3 v g - sphericalSection3 v (g * diagonal3 v ![1, (uniformizerUnit ℚ v)⁻¹, 1]) :=
  rfl

private theorem witness1_one : (witness1 v : LocalGL3 v → ℂ) 1 = 0 := by
  rw [witness1_apply, one_mul, ← mul_one (diagonal3 v ![1, (uniformizerUnit ℚ v)⁻¹, 1]),
    apply_diagonal3_mul_of_mem_principalSeries3 (sphericalSection3_mem v), torusChar3_trivial, halfModulus3_middle]
  simp

private theorem witness1_vanishes (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0)
    (h21 : gl3Entry v g 2 1 = 0) : (witness1 v : LocalGL3 v → ℂ) g = 0 :=
  apply_eq_zero_of_apply_one_eq_zero v (witness1 v).2 (witness1_one v) g h20 h10 h21

private theorem witness1_cellRep1 (x : v.adicCompletion ℚ) :
    (witness1 v : LocalGL3 v → ℂ) (cellRep1 v x) = (1 - (Ideal.absNorm v.asIdeal : ℂ)) * ballIndicator v 0 1 x := by
  rw [witness1_apply, cellRep1_mul_diagonal3, apply_diagonal3_mul_of_mem_principalSeries3 (sphericalSection3_mem v),
    torusChar3_trivial, halfModulus3_left, sphericalSection3_cellRep1, sphericalSection3_cellRep1, norm_mul,
    norm_uniformizerUnit_inv, one_mul]
  exact ball_identity v x

private def translate1 (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    ↥(principalSeries3 v (fun _ => 1)) :=
  translateVector v (upperUnipotent3 (-y) 0 0)
    (translateVector v (diagonal3 v ![1, Units.mk0 t ht, 1]) (witness1 v))

private theorem translate1_vanishes (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0) (h21 : gl3Entry v g 2 1 = 0) :
    (translate1 v y ht : LocalGL3 v → ℂ) g = 0 := by
  have h20' : gl3Entry v g 2 0 = 0 := h20
  rw [translate1, translateVector_apply, translateVector_apply]
  apply witness1_vanishes v
  · show gl3Entry v (g * upperUnipotent3 (-y) 0 0 * diagonal3 v ![1, Units.mk0 t ht, 1]) 2 0 = 0
    rw [gl3Entry_mul_diagonal3, gl3Entry_mul_upperUnipotent3_two_zero, h20', zero_mul]
  · rw [gl3Entry_mul_diagonal3, entry_one_zero_mul_upperUnipotent3, h10, zero_mul]
  · rw [gl3Entry_mul_diagonal3, entry_two_one_mul_upperUnipotent3, h20', h21, zero_mul, add_zero, zero_mul]

private theorem profile1_translate1 (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) {k : ℤ}
    (htv : Valued.v t = WithZero.exp (-(1 - k))) :
    profile1 v (translate1 v y ht : LocalGL3 v → ℂ) =
      (((‖t‖ : ℝ) : ℂ) * (1 - (Ideal.absNorm v.asIdeal : ℂ))) • ballIndicator v y k := by
  funext x
  have hb : ballIndicator v 0 1 (t * (x - y)) = ballIndicator v y k x := by
    have h := congr_fun (ballIndicator_comp_mul_left v ht htv 0 1) (x - y)
    simp only [mul_zero, sub_sub_cancel] at h
    rw [h]
    simp only [ballIndicator, sub_zero]
  rw [profile1_apply, Pi.smul_apply, smul_eq_mul, translate1, translateVector_apply, translateVector_apply,
    cellRep1_mul_upperUnipotent3, ← sub_eq_add_neg, cellRep1_mul_diagonal3,
    apply_diagonal3_mul_of_mem_principalSeries3 (witness1 v).2, torusChar3_trivial, halfModulus3_left,
    witness1_cellRep1, Units.val_mk0, hb]
  ring

private def witness2 : ↥(principalSeries3 v (fun _ => 1)) :=
  sphericalVector v -
    ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) •
      translateVector v (diagonal3 v ![1, 1, (uniformizerUnit ℚ v)⁻¹]) (sphericalVector v)

private theorem witness2_apply (g : LocalGL3 v) :
    (witness2 v : LocalGL3 v → ℂ) g =
      sphericalSection3 v g -
        ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
          sphericalSection3 v (g * diagonal3 v ![1, 1, (uniformizerUnit ℚ v)⁻¹]) :=
  rfl

private theorem witness2_one : (witness2 v : LocalGL3 v → ℂ) 1 = 0 := by
  rw [witness2_apply, one_mul, ← mul_one (diagonal3 v ![1, 1, (uniformizerUnit ℚ v)⁻¹]),
    apply_diagonal3_mul_of_mem_principalSeries3 (sphericalSection3_mem v), torusChar3_trivial, halfModulus3_right,
    norm_uniformizerUnit_inv]
  exact absNorm_cancel v _

private theorem witness2_cellRep1 (x : v.adicCompletion ℚ) : (witness2 v : LocalGL3 v → ℂ) (cellRep1 v x) = 0 := by
  rw [witness2_apply, cellRep1_mul_diagonal3_right,
    apply_diagonal3_mul_of_mem_principalSeries3 (sphericalSection3_mem v), torusChar3_trivial, halfModulus3_right,
    norm_uniformizerUnit_inv]
  exact absNorm_cancel v _

private theorem witness2_vanishes (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h21 : gl3Entry v g 2 1 = 0) :
    (witness2 v : LocalGL3 v → ℂ) g = 0 := by
  by_cases h10 : gl3Entry v g 1 0 = 0
  · exact apply_eq_zero_of_apply_one_eq_zero v (witness2 v).2 (witness2_one v) g h20 h10 h21
  · obtain ⟨_, _, _, _, w, hg⟩ := exists_eq_mul_cellRep1 v g h20 h21 h10
    rw [hg, apply_upperUnipotent3_mul_of_mem_principalSeries3 (witness2 v).2,
      apply_diagonal3_mul_of_mem_principalSeries3 (witness2 v).2, witness2_cellRep1, mul_zero]

private theorem witness2_cellRep2 (y : v.adicCompletion ℚ) :
    (witness2 v : LocalGL3 v → ℂ) (cellRep2 v y) = (1 - (Ideal.absNorm v.asIdeal : ℂ)) * ballIndicator v 0 1 y := by
  rw [witness2_apply, cellRep2_mul_diagonal3, apply_diagonal3_mul_of_mem_principalSeries3 (sphericalSection3_mem v),
    torusChar3_trivial, halfModulus3_middle, sphericalSection3_cellRep2, sphericalSection3_cellRep2, norm_mul,
    norm_uniformizerUnit_inv, one_mul, one_mul]
  exact ball_identity v y

private def translate2 (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) :
    ↥(principalSeries3 v (fun _ => 1)) :=
  translateVector v (upperUnipotent3 0 (-y) 0)
    (translateVector v (diagonal3 v ![1, 1, Units.mk0 t ht]) (witness2 v))

private theorem translate2_vanishes (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h21 : gl3Entry v g 2 1 = 0) : (translate2 v y ht : LocalGL3 v → ℂ) g = 0 := by
  have h20' : gl3Entry v g 2 0 = 0 := h20
  rw [translate2, translateVector_apply, translateVector_apply]
  apply witness2_vanishes v
  · show gl3Entry v (g * upperUnipotent3 0 (-y) 0 * diagonal3 v ![1, 1, Units.mk0 t ht]) 2 0 = 0
    rw [gl3Entry_mul_diagonal3, gl3Entry_mul_upperUnipotent3_two_zero, h20', zero_mul]
  · rw [gl3Entry_mul_diagonal3, entry_two_one_mul_upperUnipotent3, h20', h21, zero_mul, add_zero, zero_mul]

private theorem profile2_translate2 (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0) {k : ℤ}
    (htv : Valued.v t = WithZero.exp (-(1 - k))) :
    profile2 v (translate2 v y ht : LocalGL3 v → ℂ) = (1 - (Ideal.absNorm v.asIdeal : ℂ)) • ballIndicator v y k := by
  funext x
  have hb : ballIndicator v 0 1 (t * (x - y)) = ballIndicator v y k x := by
    have h := congr_fun (ballIndicator_comp_mul_left v ht htv 0 1) (x - y)
    simp only [mul_zero, sub_sub_cancel] at h
    rw [h]
    simp only [ballIndicator, sub_zero]
  rw [profile2_apply, Pi.smul_apply, smul_eq_mul, translate2, translateVector_apply, translateVector_apply,
    cellRep2_mul_upperUnipotent3, ← sub_eq_add_neg, cellRep2_mul_diagonal3,
    apply_diagonal3_mul_of_mem_principalSeries3 (witness2 v).2, torusChar3_trivial, halfModulus3_middle,
    witness2_cellRep2, Units.val_mk0, hb]
  ring

private def vanishingOnTriangular : Submodule ℂ (LocalGL3 v → ℂ) where
  carrier := {f | ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → gl3Entry v g 2 1 = 0 → f g = 0}
  zero_mem' := by
    intro g _ _ _
    rfl
  add_mem' := by
    intro f₁ f₂ h₁ h₂ g hg0 hg1 hg2
    show f₁ g + f₂ g = 0
    rw [h₁ g hg0 hg1 hg2, h₂ g hg0 hg1 hg2, add_zero]
  smul_mem' := by
    intro c f hf g hg0 hg1 hg2
    show c * f g = 0
    rw [hf g hg0 hg1 hg2, mul_zero]

private theorem mem_vanishingOnTriangular_iff (f : LocalGL3 v → ℂ) :
    f ∈ vanishingOnTriangular v ↔
      ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → gl3Entry v g 2 1 = 0 → f g = 0 :=
  Iff.rfl

private def vanishingOnParabolic : Submodule ℂ (LocalGL3 v → ℂ) where
  carrier := {f | ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → f g = 0}
  zero_mem' := by
    intro g _ _
    rfl
  add_mem' := by
    intro f₁ f₂ h₁ h₂ g hg0 hg2
    show f₁ g + f₂ g = 0
    rw [h₁ g hg0 hg2, h₂ g hg0 hg2, add_zero]
  smul_mem' := by
    intro c f hf g hg0 hg2
    show c * f g = 0
    rw [hf g hg0 hg2, mul_zero]

private theorem mem_vanishingOnParabolic_iff (f : LocalGL3 v → ℂ) :
    f ∈ vanishingOnParabolic v ↔ ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → f g = 0 :=
  Iff.rfl

private theorem apply_eq_zero_of_vanishing_on_triangular (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    (hT : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f)
    (h₂ : ∀ f : ↥(principalSeries3 v (fun _ => 1)),
      (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (f : ↥(principalSeries3 v (fun _ => 1)))
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → gl3Entry v g 2 1 = 0 →
      (f : LocalGL3 v → ℂ) g = 0) :
    Λ f = 0 := by
  have hN' : ∀ (x y z : v.adicCompletion ℚ) (h : ↥(principalSeries3 v (fun _ => 1))),
      Λ (translateVector v (upperUnipotent3 x y z) h) = Λ h := hN
  have hT' : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (h : ↥(principalSeries3 v (fun _ => 1))),
      Λ (translateVector v (diagonal3 v a) h) = torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ h := hT
  have hq1 : (1 : ℂ) - (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h := one_lt_natCard_quot v
    rw [natCard_quot_eq_absNorm] at h
    rw [sub_ne_zero]
    exact_mod_cast h.ne

  have hw : Λ (witness1 v) = 0 := by
    rw [witness1, map_sub, hT', torusChar3_trivial, halfModulus3_middle]
    simp

  let K : Submodule ℂ ↥(principalSeries3 v (fun _ => 1)) :=
    LinearMap.ker Λ ⊓ Submodule.comap (principalSeries3 v (fun _ => 1)).subtype (vanishingOnTriangular v)
  let S : Submodule ℂ (v.adicCompletion ℚ → ℂ) :=
    Submodule.map (profile1 v ∘ₗ (principalSeries3 v (fun _ => 1)).subtype) K
  have hball : ∀ (y : v.adicCompletion ℚ) (k : ℤ), ballIndicator v y k ∈ S := by
    intro y k
    obtain ⟨t, ht, htv⟩ := exists_valued_eq_exp v (-(1 - k))
    have hc : ((‖t‖ : ℝ) : ℂ) * (1 - (Ideal.absNorm v.asIdeal : ℂ)) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ht)) hq1
    have hΛ : Λ (translate1 v y ht) = 0 := by
      rw [translate1, hN', hT', hw, mul_zero]
    have hvan : (principalSeries3 v (fun _ => 1)).subtype (translate1 v y ht) ∈ vanishingOnTriangular v := by
      rw [Submodule.subtype_apply, mem_vanishingOnTriangular_iff]
      exact translate1_vanishes v y ht
    have hK : translate1 v y ht ∈ K :=
      Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hΛ, Submodule.mem_comap.mpr hvan⟩
    refine Submodule.mem_map.mpr ⟨(((‖t‖ : ℝ) : ℂ) * (1 - (Ideal.absNorm v.asIdeal : ℂ)))⁻¹ • translate1 v y ht,
      K.smul_mem _ hK, ?_⟩
    rw [map_smul, LinearMap.comp_apply, Submodule.subtype_apply, profile1_translate1 v y ht htv, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hS : stepFunctions v ≤ S := by
    refine (stepFunctions_le_span_ballIndicator v).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨⟨y, k⟩, rfl⟩
    exact hball y k
  have hf1 : (f : LocalGL3 v → ℂ) 1 = 0 :=
    hf 1 (by simp [cornerEntry, gl3Entry]) (by simp [gl3Entry]) (by simp [gl3Entry])
  obtain ⟨F, hFK, hPF⟩ := Submodule.mem_map.mp (hS (profile1_mem_stepFunctions v f.2 hf1))
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at hPF
  obtain ⟨hFker, hFvan⟩ := Submodule.mem_inf.mp hFK
  have hΛF : Λ F = 0 := LinearMap.mem_ker.mp hFker
  rw [Submodule.mem_comap, Submodule.subtype_apply, mem_vanishingOnTriangular_iff] at hFvan
  have hFv : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → gl3Entry v g 2 1 = 0 →
      (F : LocalGL3 v → ℂ) g = 0 := hFvan
  have hsub : ((f : LocalGL3 v → ℂ) - (F : LocalGL3 v → ℂ)) ∈ principalSeries3 v (fun _ => 1) :=
    (principalSeries3 v (fun _ => 1)).sub_mem f.2 F.2
  have hdiff : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 →
      ((f - F : ↥(principalSeries3 v (fun _ => 1))) : LocalGL3 v → ℂ) g = 0 := by
    intro g h20 h21
    rw [Submodule.coe_sub]
    by_cases h10 : gl3Entry v g 1 0 = 0
    · rw [Pi.sub_apply, hf g h20 h10 h21, hFv g h20 h10 h21, sub_zero]
    · obtain ⟨_, _, _, _, w, hg⟩ := exists_eq_mul_cellRep1 v g h20 h21 h10
      have hw' : ((f : LocalGL3 v → ℂ) - (F : LocalGL3 v → ℂ)) (cellRep1 v w) = 0 := by
        have h := congr_fun hPF w
        rw [profile1_apply, profile1_apply] at h
        rw [Pi.sub_apply, sub_eq_zero]
        exact h.symm
      rw [hg, apply_upperUnipotent3_mul_of_mem_principalSeries3 hsub, apply_diagonal3_mul_of_mem_principalSeries3 hsub,
        hw', mul_zero]
  have h := h₂ (f - F) hdiff
  rwa [map_sub, hΛF, sub_zero] at h

private theorem apply_eq_zero_of_vanishing_on_parabolic (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    (hT : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f)
    (h₃ : ∀ f : ↥(principalSeries3 v (fun _ => 1)),
      (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 →
        (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (f : ↥(principalSeries3 v (fun _ => 1)))
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → (f : LocalGL3 v → ℂ) g = 0) :
    Λ f = 0 := by
  have hN' : ∀ (x y z : v.adicCompletion ℚ) (h : ↥(principalSeries3 v (fun _ => 1))),
      Λ (translateVector v (upperUnipotent3 x y z) h) = Λ h := hN
  have hT' : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (h : ↥(principalSeries3 v (fun _ => 1))),
      Λ (translateVector v (diagonal3 v a) h) = torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ h := hT
  have hq1 : (1 : ℂ) - (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h := one_lt_natCard_quot v
    rw [natCard_quot_eq_absNorm] at h
    rw [sub_ne_zero]
    exact_mod_cast h.ne

  have hw : Λ (witness2 v) = 0 := by
    rw [witness2, map_sub, map_smul, hT', torusChar3_trivial, halfModulus3_right, norm_uniformizerUnit_inv,
      smul_eq_mul]
    exact absNorm_cancel v _
  let K : Submodule ℂ ↥(principalSeries3 v (fun _ => 1)) :=
    LinearMap.ker Λ ⊓ Submodule.comap (principalSeries3 v (fun _ => 1)).subtype (vanishingOnParabolic v)
  let S : Submodule ℂ (v.adicCompletion ℚ → ℂ) :=
    Submodule.map (profile2 v ∘ₗ (principalSeries3 v (fun _ => 1)).subtype) K
  have hball : ∀ (y : v.adicCompletion ℚ) (k : ℤ), ballIndicator v y k ∈ S := by
    intro y k
    obtain ⟨t, ht, htv⟩ := exists_valued_eq_exp v (-(1 - k))
    have hΛ : Λ (translate2 v y ht) = 0 := by
      rw [translate2, hN', hT', hw, mul_zero]
    have hvan : (principalSeries3 v (fun _ => 1)).subtype (translate2 v y ht) ∈ vanishingOnParabolic v := by
      rw [Submodule.subtype_apply, mem_vanishingOnParabolic_iff]
      exact translate2_vanishes v y ht
    have hK : translate2 v y ht ∈ K :=
      Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hΛ, Submodule.mem_comap.mpr hvan⟩
    refine Submodule.mem_map.mpr ⟨(1 - (Ideal.absNorm v.asIdeal : ℂ))⁻¹ • translate2 v y ht, K.smul_mem _ hK, ?_⟩
    rw [map_smul, LinearMap.comp_apply, Submodule.subtype_apply, profile2_translate2 v y ht htv, smul_smul,
      inv_mul_cancel₀ hq1, one_smul]
  have hS : stepFunctions v ≤ S := by
    refine (stepFunctions_le_span_ballIndicator v).trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨⟨y, k⟩, rfl⟩
    exact hball y k
  have hf1 : (f : LocalGL3 v → ℂ) 1 = 0 := hf 1 (by simp [cornerEntry, gl3Entry]) (by simp [gl3Entry])
  obtain ⟨F, hFK, hPF⟩ := Submodule.mem_map.mp (hS (profile2_mem_stepFunctions v f.2 hf1))
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at hPF
  obtain ⟨hFker, hFvan⟩ := Submodule.mem_inf.mp hFK
  have hΛF : Λ F = 0 := LinearMap.mem_ker.mp hFker
  rw [Submodule.mem_comap, Submodule.subtype_apply, mem_vanishingOnParabolic_iff] at hFvan
  have hFv : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → (F : LocalGL3 v → ℂ) g = 0 := hFvan
  have hsub : ((f : LocalGL3 v → ℂ) - (F : LocalGL3 v → ℂ)) ∈ principalSeries3 v (fun _ => 1) :=
    (principalSeries3 v (fun _ => 1)).sub_mem f.2 F.2
  have hdiff : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 →
      ((f - F : ↥(principalSeries3 v (fun _ => 1))) : LocalGL3 v → ℂ) g = 0 := by
    intro g h20 hprod
    rw [Submodule.coe_sub]
    by_cases h21 : gl3Entry v g 2 1 = 0
    · rw [Pi.sub_apply, hf g h20 h21, hFv g h20 h21, sub_zero]
    · have h10 : gl3Entry v g 1 0 = 0 := (mul_eq_zero.mp hprod).resolve_right h21
      obtain ⟨_, _, _, _, w, hg⟩ := exists_eq_mul_cellRep2 v g h20 h10 h21
      have hw' : ((f : LocalGL3 v → ℂ) - (F : LocalGL3 v → ℂ)) (cellRep2 v w) = 0 := by
        have h := congr_fun hPF w
        rw [profile2_apply, profile2_apply] at h
        rw [Pi.sub_apply, sub_eq_zero]
        exact h.symm
      rw [hg, apply_upperUnipotent3_mul_of_mem_principalSeries3 hsub, apply_diagonal3_mul_of_mem_principalSeries3 hsub,
        hw', mul_zero]
  have h := h₃ (f - F) hdiff
  rwa [map_sub, hΛF, sub_zero] at h

end SphericalSection

end LanglandsTunnell.CubicInduction

end JoinPiece_Spherical

section JoinPiece_SphericalValues

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Det_cornerCellPoint (y z : v.adicCompletion ℚ) : gl3Det v (cornerCellPoint v y z) = 1 := by
  simp [gl3Det, cornerCellPoint_coe, Matrix.det_fin_three]

private theorem gl3Det_minorCellPoint (u w : v.adicCompletion ℚ) : gl3Det v (minorCellPoint v u w) = 1 := by
  simp [gl3Det, minorCellPoint_coe, Matrix.det_fin_three]

private theorem gl3Det_openCellPoint (x y z : v.adicCompletion ℚ) : gl3Det v (openCellPoint v x y z) = -1 := by
  simp [gl3Det, openCellPoint_coe, Matrix.det_fin_three]

private theorem sphericalSection3_cornerCellPoint (y z : v.adicCompletion ℚ) :
    sphericalSection3 v (cornerCellPoint v y z)
      = (((max (max 1 ‖y‖) ‖z‖ * max 1 ‖y‖)⁻¹ : ℝ) : ℂ) := by
  simp only [sphericalSection3, minorNorm, bottomNorm, rightMinor, gl3Det_cornerCellPoint, lowerMinor, outerMinor,
    gl3Entry, cornerCellPoint_coe]
  simp [one_div]

private theorem sphericalSection3_minorCellPoint (u w : v.adicCompletion ℚ) :
    sphericalSection3 v (minorCellPoint v u w)
      = (((max 1 ‖u‖ * max (max 1 ‖u‖) ‖w‖)⁻¹ : ℝ) : ℂ) := by
  simp only [sphericalSection3, minorNorm, bottomNorm, rightMinor, gl3Det_minorCellPoint, lowerMinor, outerMinor,
    gl3Entry, minorCellPoint_coe]
  simp [one_div]

private theorem sphericalSection3_openCellPoint (x y z : v.adicCompletion ℚ) :
    sphericalSection3 v (openCellPoint v x y z)
      = (((max (max 1 ‖y‖) ‖z - y * x‖ * max (max 1 ‖x‖) ‖z‖)⁻¹ : ℝ) : ℂ) := by
  simp only [sphericalSection3, minorNorm, bottomNorm, rightMinor, gl3Det_openCellPoint, lowerMinor, outerMinor,
    gl3Entry, openCellPoint_coe]
  simp [one_div]

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_SphericalValues

section JoinPiece_LinkLayer

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TransversalAlgebra

variable {G : Type*} [Group G]

private theorem isTransversal_mul [DecidableEq G] {H H' H'' : Subgroup G} (hle : H' ≤ H) (hle' : H'' ≤ H')
    {T S : Finset G} (hT : IsTransversal H H' T) (hS : IsTransversal H' H'' S) :
    IsTransversal H H'' ((T ×ˢ S).image fun p => p.1 * p.2) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨⟨τ, s⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hτ, hs⟩ := Finset.mem_product.1 hp
    exact H.mul_mem (hT.1 τ hτ) (hle (hS.1 s hs))
  · intro k hk
    obtain ⟨τ, ⟨hτ, h', hh', hkτ⟩, hτu⟩ := hT.2 k hk
    obtain ⟨s, ⟨hs, h'', hh'', hh's⟩, hsu⟩ := hS.2 h' hh'
    refine ⟨τ * s, ⟨Finset.mem_image.2 ⟨⟨τ, s⟩, Finset.mem_product.2 ⟨hτ, hs⟩, rfl⟩, h'', hh'', ?_⟩, ?_⟩
    · rw [hkτ, hh's, mul_assoc]
    · rintro x ⟨hx, g'', hg'', hkx⟩
      obtain ⟨⟨τ₂, s₂⟩, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hτ₂, hs₂⟩ := Finset.mem_product.1 hp
      have hτ₂τ : τ₂ = τ :=
        hτu τ₂ ⟨hτ₂, s₂ * g'', H'.mul_mem (hS.1 s₂ hs₂) (hle' hg''), by rw [hkx, mul_assoc]⟩
      subst hτ₂τ
      have hh'eq : h' = s₂ * g'' := by
        have h1 : τ₂ * h' = τ₂ * (s₂ * g'') := by rw [← hkτ, hkx, mul_assoc]
        exact mul_left_cancel h1
      rw [hsu s₂ ⟨hs₂, g'', hg'', hh'eq⟩]

private theorem mul_eq_mul_imp_eq_of_isTransversal {H H' : Subgroup G} (hle : H' ≤ H) {T S : Finset G}
    (hT : IsTransversal H H' T) (hS : ∀ s ∈ S, s ∈ H') :
    ∀ p ∈ T ×ˢ S, ∀ q ∈ T ×ˢ S, p.1 * p.2 = q.1 * q.2 → p = q := by
  rintro ⟨τ₁, s₁⟩ hp ⟨τ₂, s₂⟩ hq heq
  obtain ⟨hτ₁, hs₁⟩ := Finset.mem_product.1 hp
  obtain ⟨hτ₂, hs₂⟩ := Finset.mem_product.1 hq
  have heq' : τ₁ * s₁ = τ₂ * s₂ := heq
  have hx : τ₁ * s₁ ∈ H := H.mul_mem (hT.1 τ₁ hτ₁) (hle (hS s₁ hs₁))

  have hττ : τ₁ = τ₂ :=
    ((hT.2 _ hx).unique ⟨hτ₁, s₁, hS s₁ hs₁, rfl⟩ ⟨hτ₂, s₂, hS s₂ hs₂, heq'⟩)
  subst hττ
  have hss : s₁ = s₂ := mul_left_cancel heq'
  rw [hss]

private theorem sum_eq_card_mul_sum_of_isTransversal [DecidableEq G] {H H₂ H₁ : Subgroup G} (hle : H₂ ≤ H)
    (hle' : H₁ ≤ H₂) {S₁ S₂ R : Finset G} (hS₁ : IsTransversal H H₁ S₁) (hS₂ : IsTransversal H H₂ S₂)
    (hR : IsTransversal H₂ H₁ R) {f : G → ℂ} (hf : ∀ s, ∀ h ∈ H₂, f (s * h) = f s) :
    ∑ s ∈ S₁, f s = (R.card : ℂ) * ∑ s ∈ S₂, f s := by
  have hf₁ : ∀ s, ∀ h ∈ H₁, f (s * h) = f s := fun s h hh => hf s h (hle' hh)
  rw [sum_eq_of_isTransversal hS₁ (isTransversal_mul hle hle' hS₂ hR) hf₁,
    Finset.sum_image (mul_eq_mul_imp_eq_of_isTransversal hle hS₂ hR.1), Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact (Finset.sum_congr rfl fun r hr => hf τ r (hR.1 r hr)).trans (by rw [Finset.sum_const, nsmul_eq_mul])

private theorem card_ne_zero_of_isTransversal {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S) :
    (S.card : ℂ) ≠ 0 := by
  obtain ⟨s, ⟨hs, -⟩, -⟩ := hS.2 1 H.one_mem
  exact_mod_cast (Finset.card_pos.2 ⟨s, hs⟩).ne'

end TransversalAlgebra

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def cellSum (w : LocalGL3 v) (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) : ℂ :=
  ∑ s ∈ S, f (w * s)

private theorem cellSum_sub (w : LocalGL3 v) (S : Finset (LocalGL3 v)) (f g : LocalGL3 v → ℂ) :
    cellSum v w S (f - g) = cellSum v w S f - cellSum v w S g := by
  simp only [cellSum, Pi.sub_apply, Finset.sum_sub_distrib]

private theorem cellSum_smul (w : LocalGL3 v) (S : Finset (LocalGL3 v)) (c : ℂ) (f : LocalGL3 v → ℂ) :
    cellSum v w S (c • f) = c * cellSum v w S f := by
  simp only [cellSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

private theorem cellSum_eq_zero_of_forall {w : LocalGL3 v} {S : Finset (LocalGL3 v)} {f : LocalGL3 v → ℂ}
    (h : ∀ s ∈ S, f (w * s) = 0) : cellSum v w S f = 0 :=
  Finset.sum_eq_zero h

section Generic

variable {G : Type*} [Group G]

private theorem
    isTransversal_image_mul_left [DecidableEq G] {K L : Subgroup G} {S : Finset G} (hS : IsTransversal K L S)
    {u : G} (hu : u ∈ K) : IsTransversal K L (S.image fun s => u * s) := by
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
    exact K.mul_mem hu (hS.1 s hs)
  · obtain ⟨s, ⟨hsS, κ, hκ, hxs⟩, huniq⟩ := hS.2 (u⁻¹ * x) (K.mul_mem (K.inv_mem hu) hx)
    refine ⟨u * s, ⟨Finset.mem_image_of_mem _ hsS, κ, hκ, ?_⟩, ?_⟩
    · rw [mul_assoc, ← hxs, mul_inv_cancel_left]
    · rintro y ⟨hy, κ', hκ', hxy⟩
      obtain ⟨s', hs'S, rfl⟩ := Finset.mem_image.1 hy
      have h1 : u⁻¹ * x = s' * κ' := by rw [hxy, mul_assoc, inv_mul_cancel_left]
      rw [huniq s' ⟨hs'S, κ', hκ', h1⟩]

end Generic

private theorem
    levelAvg_apply_mul_of_mem {K L : Subgroup (LocalGL3 v)} {S : Finset (LocalGL3 v)} (hS : IsTransversal K L S)
    {f : LocalGL3 v → ℂ} (hf : ∀ κ ∈ L, ∀ g, f (g * κ) = f g) (w : LocalGL3 v) {u : LocalGL3 v} (hu : u ∈ K) :
    levelAvg v S f (w * u) = (S.card : ℂ)⁻¹ * cellSum v w S f := by
  classical
  have hinj : Function.Injective fun s : LocalGL3 v => u * s := mul_right_injective u
  have h1 : levelAvg v S f (w * u) = levelAvg v (S.image fun s => u * s) f w := by
    rw [levelAvg_apply, levelAvg_apply, Finset.card_image_of_injective _ hinj, Finset.sum_image hinj.injOn]
    simp only [mul_assoc]
  have h2 : levelAvg v (S.image fun s => u * s) f = levelAvg v S f :=
    levelAvg_eq_of_isTransversal v (isTransversal_image_mul_left hS hu) hS hf
  rw [h1, h2, levelAvg_apply, cellSum]

private theorem levelAvg_apply_mul_of_not_mem {U K : Subgroup (LocalGL3 v)} (hKU : K ≤ U) {S : Finset (LocalGL3 v)}
    (hSK : ∀ s ∈ S, s ∈ K) {f : LocalGL3 v → ℂ} {w : LocalGL3 v} (hsupp : ∀ u ∈ U, u ∉ K → f (w * u) = 0)
    {u : LocalGL3 v} (huU : u ∈ U) (hu : u ∉ K) : levelAvg v S f (w * u) = 0 := by
  rw [levelAvg_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s hs => ?_)
  rw [mul_assoc]
  refine hsupp _ (U.mul_mem huU (hKU (hSK s hs))) fun hus => hu ?_
  simpa only [mul_inv_cancel_right] using K.mul_mem hus (K.inv_mem (hSK s hs))

private theorem apply_levelAvgLin_eq {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    {U : Subgroup (LocalGL3 v)}
    (hΛU : ∀ u ∈ U, ∀ f : ↥(principalSeries3 v χ),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) u f, rightTranslate_mem_principalSeries3 f.2 u⟩ = Λ f)
    {S : Finset (LocalGL3 v)} (hSU : ∀ s ∈ S, s ∈ U) (hScard : S.card ≠ 0) (f : ↥(principalSeries3 v χ)) :
    Λ (levelAvgLin v S χ f) = Λ f := by
  simp only [levelAvgLin, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul]
  have h2 : ∀ s ∈ S,
      Λ ((gl3AmbientRightTranslate (R := ℂ) s).restrict (p := principalSeries3 v χ) (q := principalSeries3 v χ)
        (fun _ hf => rightTranslate_mem_principalSeries3 hf s) f) = Λ f :=
    fun s hs => hΛU s (hSU s hs) f
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hScard), one_mul]

private theorem apply_eq_zero_of_cellSum_ne_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) {U K L : Subgroup (LocalGL3 v)} (hKU : K ≤ U)
    (hΛU : ∀ u ∈ U, ∀ f : ↥(principalSeries3 v χ),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) u f, rightTranslate_mem_principalSeries3 f.2 u⟩ = Λ f)
    {Z Z' : Set (LocalGL3 v)} (hZU : ∀ g ∈ Z, ∀ u ∈ U, g * u ∈ Z) (w : LocalGL3 v)
    (hcover : ∀ h : LocalGL3 v → ℂ, h ∈ principalSeries3 v χ → (∀ g ∈ Z, h g = 0) → (∀ u ∈ U, h (w * u) = 0) →
      ∀ g ∈ Z', h g = 0)
    {S : Finset (LocalGL3 v)} (hS : IsTransversal K L S)
    (hkill : ∀ h : ↥(principalSeries3 v χ), (∀ g ∈ Z', (h : LocalGL3 v → ℂ) g = 0) → Λ h = 0)
    (ψ : ↥(principalSeries3 v χ)) (hψZ : ∀ g ∈ Z, (ψ : LocalGL3 v → ℂ) g = 0)
    (hψL : ∀ κ ∈ L, ∀ g, (ψ : LocalGL3 v → ℂ) (g * κ) = (ψ : LocalGL3 v → ℂ) g)
    (hψK : ∀ u ∈ U, u ∉ K → (ψ : LocalGL3 v → ℂ) (w * u) = 0) (hΛψ : Λ ψ = 0)
    (hψS : cellSum v w S ψ ≠ 0)
    (f : ↥(principalSeries3 v χ)) (hfZ : ∀ g ∈ Z, (f : LocalGL3 v → ℂ) g = 0)
    (hfL : ∀ κ ∈ L, ∀ g, (f : LocalGL3 v → ℂ) (g * κ) = (f : LocalGL3 v → ℂ) g)
    (hfK : ∀ u ∈ U, u ∉ K → (f : LocalGL3 v → ℂ) (w * u) = 0) : Λ f = 0 := by
  set c : ℂ := cellSum v w S f / cellSum v w S ψ with hc
  set g : ↥(principalSeries3 v χ) := f - c • ψ with hg
  have hgfun : (g : LocalGL3 v → ℂ) = (f : LocalGL3 v → ℂ) - c • (ψ : LocalGL3 v → ℂ) := rfl
  have hSK : ∀ s ∈ S, s ∈ K := hS.1
  have hScard : S.card ≠ 0 := Finset.card_ne_zero.2 (Finset.nonempty_of_sum_ne_zero hψS)

  have hgS : cellSum v w S g = 0 := by
    rw [hgfun, cellSum_sub, cellSum_smul, hc, div_mul_cancel₀ _ hψS, sub_self]

  have hgU : ∀ u ∈ U, levelAvg v S g (w * u) = 0 := by
    intro u hu
    by_cases huK : u ∈ K
    · rw [levelAvg_apply_mul_of_mem v hS (fun κ hκ x => by
          simp only [hgfun, Pi.sub_apply, Pi.smul_apply, hfL κ hκ x, hψL κ hκ x]) w huK, hgS, mul_zero]
    · refine levelAvg_apply_mul_of_not_mem v hKU hSK (fun u' hu' hu'K => ?_) hu huK
      simp only [hgfun, Pi.sub_apply, Pi.smul_apply, hfK u' hu' hu'K, hψK u' hu' hu'K, smul_zero, sub_zero]

  have hgZ : ∀ x ∈ Z, levelAvg v S g x = 0 := by
    intro x hx
    rw [levelAvg_apply]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s hs => ?_)
    have hxs : x * s ∈ Z := hZU x hx s (hKU (hSK s hs))
    simp only [hgfun, Pi.sub_apply, Pi.smul_apply, hfZ _ hxs, hψZ _ hxs, smul_zero, sub_zero]
  have hgZ' : ∀ x ∈ Z', ((levelAvgLin v S χ g : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) x = 0 := by
    rw [coe_levelAvgLin_apply]
    exact hcover _ (levelAvg_mem_principalSeries3 v S g.2) hgZ hgU
  have hΛg : Λ g = 0 := by
    rw [← apply_levelAvgLin_eq v Λ hΛU (fun s hs => hKU (hSK s hs)) hScard g]
    exact hkill _ hgZ'

  rw [hg, map_sub, map_smul, hΛψ, smul_zero, sub_zero] at hΛg
  exact hΛg

private theorem forall_mem_apply_rightTranslate_eq_of_forall_upperUnipotent3
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
        rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    {U : Subgroup (LocalGL3 v)} (hU : ∀ u ∈ U, ∃ x y z : v.adicCompletion ℚ, u = upperUnipotent3 x y z) :
    ∀ u ∈ U, ∀ f : ↥(principalSeries3 v χ),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) u f, rightTranslate_mem_principalSeries3 f.2 u⟩ = Λ f := by
  intro u hu f
  obtain ⟨x, y, z, rfl⟩ := hU u hu
  exact hN x y z f

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem cellSum_eq_card_mul_cellSum {K L L' : Subgroup (LocalGL3 v)} (hLK : L ≤ K) (hL'L : L' ≤ L)
    {S S' R : Finset (LocalGL3 v)} (hS' : IsTransversal K L' S') (hS : IsTransversal K L S) (hR : IsTransversal L L' R)
    (w : LocalGL3 v) {f : LocalGL3 v → ℂ} (hf : ∀ κ ∈ L, ∀ g, f (g * κ) = f g) :
    cellSum v w S' f = (R.card : ℂ) * cellSum v w S f := by
  classical
  exact sum_eq_card_mul_sum_of_isTransversal hLK hL'L hS' hS hR (f := fun s => f (w * s))
    fun s h hh => by simp only [← mul_assoc, hf h hh]

private theorem cellSum_ne_zero_of_refine {K L L' : Subgroup (LocalGL3 v)} (hLK : L ≤ K) (hL'L : L' ≤ L)
    {S S' R : Finset (LocalGL3 v)} (hS' : IsTransversal K L' S') (hS : IsTransversal K L S) (hR : IsTransversal L L' R)
    (w : LocalGL3 v) {f : LocalGL3 v → ℂ} (hf : ∀ κ ∈ L, ∀ g, f (g * κ) = f g) (h : cellSum v w S f ≠ 0) :
    cellSum v w S' f ≠ 0 := by
  rw [cellSum_eq_card_mul_cellSum v hLK hL'L hS' hS hR w hf]
  exact mul_ne_zero (card_ne_zero_of_isTransversal hR) h

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def ballIndicatorAt (j : ℤ) (x : v.adicCompletion ℚ) : ℂ :=
  if Valued.v x ≤ WithZero.exp (-j) then 1 else 0

private theorem ballIndicatorAt_of_le {j : ℤ} {x : v.adicCompletion ℚ} (h : Valued.v x ≤ WithZero.exp (-j)) :
    ballIndicatorAt v j x = 1 := if_pos h

private theorem ballIndicatorAt_of_not_le {j : ℤ} {x : v.adicCompletion ℚ} (h : ¬ Valued.v x ≤ WithZero.exp (-j)) :
    ballIndicatorAt v j x = 0 := if_neg h

private theorem ballIndicatorAt_eq_of_sub_mem {j m : ℤ} (hjm : j ≤ m) {x y : v.adicCompletion ℚ}
    (h : Valued.v (x - y) ≤ WithZero.exp (-m)) : ballIndicatorAt v j x = ballIndicatorAt v j y := by
  have hxy : Valued.v (x - y) ≤ WithZero.exp (-j) := h.trans (WithZero.exp_le_exp.2 (neg_le_neg hjm))
  unfold ballIndicatorAt
  by_cases hy : Valued.v y ≤ WithZero.exp (-j)
  · have hx : Valued.v x ≤ WithZero.exp (-j) := by
      have := (Valued.v.map_add (x - y) y).trans (max_le hxy hy)
      simpa only [sub_add_cancel] using this
    rw [if_pos hx, if_pos hy]
  · have hx : ¬ Valued.v x ≤ WithZero.exp (-j) := fun hx => hy (by
      have h' : Valued.v (y - x) ≤ WithZero.exp (-j) := by rw [← neg_sub x y, Valued.v.map_neg]; exact hxy
      have := (Valued.v.map_add (y - x) x).trans (max_le h' hx)
      simpa only [sub_add_cancel] using this)
    rw [if_neg hx, if_neg hy]

private theorem sum_ballIndicatorAt_of_representatives {k j m : ℤ} (hkj : k ≤ j) (hjm : j ≤ m)
    {X : Finset (v.adicCompletion ℚ)}
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) :
    ∑ r ∈ X, ballIndicatorAt v j r = ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ) ^ (m - j).toNat := by
  obtain ⟨Y, hY, hY', hYcard⟩ := exists_finset_ball_representatives v j m hjm
  have hsupp : ∀ x, ballIndicatorAt v j x ≠ 0 → Valued.v x ≤ WithZero.exp (-j) := fun x hx =>
    by_contra fun h => hx (ballIndicatorAt_of_not_le v h)
  rw [sum_eq_sum_of_ball_representatives_of_le v hkj hjm hsupp (fun x y h => ballIndicatorAt_eq_of_sub_mem v hjm h)
      hY hY' hX',
    Finset.sum_congr rfl fun r hr => ballIndicatorAt_of_le v (hY r hr), Finset.sum_const, nsmul_eq_mul, mul_one,
    hYcard, Nat.cast_pow]

private theorem cellSum_levelAvg_of_forall {w : LocalGL3 v} {S T : Finset (LocalGL3 v)} (hT : T.Nonempty)
    {f : LocalGL3 v → ℂ} (h : ∀ t ∈ T, cellSum v w S (gl3AmbientRightTranslate (R := ℂ) t f) = cellSum v w S f) :
    cellSum v w S (levelAvg v T f) = cellSum v w S f := by
  have hcard : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_pos.ne'
  have hsum : ∀ s, levelAvg v T f (w * s) =
      (T.card : ℂ)⁻¹ * ∑ t ∈ T, gl3AmbientRightTranslate (R := ℂ) t f (w * s) := by
    intro s
    rw [levelAvg_apply]
    congr 1
  simp only [cellSum] at h ⊢
  rw [Finset.sum_congr rfl fun s _ => hsum s, ← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun t ht => h t ht, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard,
    one_mul]

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem sum_sum_ballIndicatorAt_mul {k₁ j₁ m₁ k₂ j₂ m₂ : ℤ} (hkj₁ : k₁ ≤ j₁) (hjm₁ : j₁ ≤ m₁) (hkj₂ : k₂ ≤ j₂)
    (hjm₂ : j₂ ≤ m₂) {Y Z : Finset (v.adicCompletion ℚ)}
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k₁) →
      ∃! r, r ∈ Y ∧ Valued.v (x - r) ≤ WithZero.exp (-m₁))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k₂) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-m₂)) :
    ∑ y ∈ Y, ∑ z ∈ Z, ballIndicatorAt v j₁ y * ballIndicatorAt v j₂ z =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ) ^ (m₁ - j₁).toNat *
        ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ) ^ (m₂ - j₂).toNat := by
  rw [← Finset.sum_mul_sum, sum_ballIndicatorAt_of_representatives v hkj₁ hjm₁ hY',
    sum_ballIndicatorAt_of_representatives v hkj₂ hjm₂ hZ']

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable abbrev residueCardC : ℂ := ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ)

private theorem card_representatives_eq {N : ℕ} {Y : Finset (v.adicCompletion ℚ)}
    (hY : ∀ r ∈ Y, Valued.v r ≤ WithZero.exp (-(0 : ℤ)))
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(0 : ℤ)) →
      ∃! r, r ∈ Y ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) :
    (Y.card : ℂ) = residueCardC v ^ N := by
  have h := sum_ballIndicatorAt_of_representatives v (le_refl (0 : ℤ)) (by exact_mod_cast N.zero_le) hY'
  rw [Finset.sum_congr rfl fun r hr => ballIndicatorAt_of_le v (hY r hr), Finset.sum_const, nsmul_eq_mul,
    mul_one] at h
  rw [h]
  congr 1

private theorem sum_sum_corner_word {ky kz : ℤ} (hky : ky ≤ 0) (hkz : kz ≤ 0) {N : ℕ} (hN : 1 ≤ N)
    {Y Z : Finset (v.adicCompletion ℚ)}
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ky) →
      ∃! r, r ∈ Y ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-kz) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    (hq : residueCardC v ≠ 0) {F : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ}
    (hF : ∀ y ∈ Y, ∀ z ∈ Z, F y z = ballIndicatorAt v 0 y *
      ((residueCardC v - 1) / residueCardC v ^ 2 * ballIndicatorAt v 0 z -
        (residueCardC v - 1) * ballIndicatorAt v 1 z)) :
    ∑ y ∈ Y, ∑ z ∈ Z, F y z = -(residueCardC v - 1) ^ 2 * (residueCardC v ^ (N - 1)) ^ 2 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hY0 : ∑ y ∈ Y, ballIndicatorAt v 0 y = residueCardC v ^ (M + 1) := by
    rw [sum_ballIndicatorAt_of_representatives v hky (by push_cast; linarith) hY']
    congr 1
  have hZ0 : ∑ z ∈ Z, ballIndicatorAt v 0 z = residueCardC v ^ (M + 1) := by
    rw [sum_ballIndicatorAt_of_representatives v hkz (by push_cast; linarith) hZ']
    congr 1
  have hZ1 : ∑ z ∈ Z, ballIndicatorAt v 1 z = residueCardC v ^ M := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hZ']
    congr 1
    omega
  have hinner : ∀ y ∈ Y, ∑ z ∈ Z, F y z = ballIndicatorAt v 0 y *
      ((residueCardC v - 1) / residueCardC v ^ 2 * residueCardC v ^ (M + 1) -
        (residueCardC v - 1) * residueCardC v ^ M) := by
    intro y hy
    rw [Finset.sum_congr rfl fun z hz => hF y hy z hz, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hZ0, hZ1]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, hY0, Nat.add_sub_cancel]
  field_simp
  ring

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem sum_sum_minor_word {ku kw : ℤ} (hku : ku ≤ 0) (hkw : kw ≤ 0) {N : ℕ} (hN : 2 ≤ N)
    {U W : Finset (v.adicCompletion ℚ)}
    (hU' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ku) →
      ∃! r, r ∈ U ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    (hW' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-kw) →
      ∃! r, r ∈ W ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    {F : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ} {ρ : v.adicCompletion ℚ → ℂ}
    (hF : ∀ u ∈ U, ∀ w ∈ W, F u w =
      (1 - residueCardC v) * (ρ w + residueCardC v * ballIndicatorAt v 1 w) * ballIndicatorAt v 1 u +
        (residueCardC v - 1) * residueCardC v *
          (ρ w + (residueCardC v - 1) * ballIndicatorAt v 1 w + residueCardC v ^ 2 * ballIndicatorAt v 2 w) *
            ballIndicatorAt v 2 u) :
    ∑ w ∈ W, ∑ u ∈ U, F u w = (residueCardC v - 1) ^ 2 * (residueCardC v ^ (N - 1)) ^ 2 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hU1 : ∑ u ∈ U, ballIndicatorAt v 1 u = residueCardC v ^ (M + 1) := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hU']
    congr 1
    omega
  have hU2 : ∑ u ∈ U, ballIndicatorAt v 2 u = residueCardC v ^ M := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hU']
    congr 1
    omega
  have hW1 : ∑ w ∈ W, ballIndicatorAt v 1 w = residueCardC v ^ (M + 1) := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hW']
    congr 1
    omega
  have hW2 : ∑ w ∈ W, ballIndicatorAt v 2 w = residueCardC v ^ M := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hW']
    congr 1
    omega
  have hinner : ∀ w ∈ W, ∑ u ∈ U, F u w = (residueCardC v - 1) * residueCardC v ^ (M + 1) *
      (-ballIndicatorAt v 1 w + residueCardC v ^ 2 * ballIndicatorAt v 2 w) := by
    intro w hw
    rw [Finset.sum_congr rfl fun u hu => hF u hu w hw, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hU1,
      hU2]
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    hW1, hW2, show M + 2 - 1 = M + 1 by omega]
  ring

end LanglandsTunnell.CubicInduction

end JoinPiece_LinkLayer

section JoinPiece_CellTransport

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem forall_mem_upperUnipotentSubgroup_iff_conj {Bx By Bz : AddSubgroup (v.adicCompletion ℚ)}
    {h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz} {a b c : v.adicCompletion ℚ} (hb : ∀ x ∈ Bx, x * b ∈ Bz)
    (ha : ∀ y ∈ By, a * y ∈ Bz) :
    ∀ g, g ∈ upperUnipotentSubgroup v Bx By Bz h
      ↔ (upperUnipotent3 a b c : LocalGL3 v)⁻¹ * g * upperUnipotent3 a b c ∈ upperUnipotentSubgroup v Bx By Bz h := by
  refine forall_mem_iff_conj_mem ?_ ?_
  · intro g hg
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hg
    rw [inv_mul_upperUnipotent3_mul]
    exact upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hx, hy, Bz.sub_mem (Bz.add_mem hz (hb x hx)) (ha y hy)⟩
  · intro g hg
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hg
    rw [upperUnipotent3_mul_mul_inv]
    exact upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hx, hy, Bz.sub_mem (Bz.add_mem hz (ha y hy)) (hb x hx)⟩

private theorem cellSum_rightTranslate_eq_of_conj_mul {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    {K L : Subgroup (LocalGL3 v)} {S : Finset (LocalGL3 v)} (hS : IsTransversal K L S)
    (hfL : ∀ κ ∈ L, ∀ g, f (g * κ) = f g) {w k₁ k₂ : LocalGL3 v} {p q r : v.adicCompletion ℚ}
    (hstab : w * k₁ = upperUnipotent3 p q r * w) (hK₁ : ∀ g, g ∈ K ↔ k₁⁻¹ * g * k₁ ∈ K)
    (hL₁ : ∀ g, g ∈ L ↔ k₁⁻¹ * g * k₁ ∈ L) (hk₂ : k₂ ∈ K) (hL₂ : ∀ g, g ∈ L ↔ k₂⁻¹ * g * k₂ ∈ L) :
    cellSum v w S (gl3AmbientRightTranslate (R := ℂ) (k₁ * k₂) f) = cellSum v w S f := by
  classical
  unfold cellSum
  simp only [gl3AmbientRightTranslate_apply]
  exact sum_mul_right_eq_of_conj_mul hS hK₁ hL₁ hk₂ hL₂ (apply_mul_mul_eq_of_mem_principalSeries3 hf hstab k₂)
    fun s κ hκ => by rw [← mul_assoc, hfL κ hκ]

private theorem cellSum_corner_rightTranslate {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    {By Bz By' Bz' : AddSubgroup (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hS : IsTransversal (upperUnipotentSubgroup v ⊥ By Bz (forall_mem_bot_mul_mem By Bz))
      (upperUnipotentSubgroup v ⊥ By' Bz' (forall_mem_bot_mul_mem By' Bz')) S)
    (hfL : ∀ κ ∈ upperUnipotentSubgroup v ⊥ By' Bz' (forall_mem_bot_mul_mem By' Bz'), ∀ g, f (g * κ) = f g)
    {a c d : v.adicCompletion ℚ} (ha : ∀ y ∈ By, a * y ∈ Bz) (ha' : ∀ y ∈ By', a * y ∈ Bz') (hc : c ∈ By)
    (hd : d ∈ Bz) :
    cellSum v (threeCycle v) S (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 a c d) f)
      = cellSum v (threeCycle v) S f := by
  have hsplit : (upperUnipotent3 a c d : LocalGL3 v) = upperUnipotent3 a 0 0 * upperUnipotent3 0 c (d - a * c) := by
    rw [upperUnipotent3_mul_upperUnipotent3]
    congr 1 <;> ring
  rw [hsplit]
  refine cellSum_rightTranslate_eq_of_conj_mul hf hS hfL (threeCycle_mul_upperUnipotent3_stab v a)
    (forall_mem_upperUnipotentSubgroup_iff_conj ?_ ha) (forall_mem_upperUnipotentSubgroup_iff_conj ?_ ha')
    (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨AddSubgroup.mem_bot.2 rfl, hc, Bz.sub_mem hd (ha c hc)⟩)
    (forall_mem_upperUnipotentSubgroup_iff_conj ?_ ?_)
  · intro x hx
    rw [AddSubgroup.mem_bot.1 hx, zero_mul]
    exact Bz.zero_mem
  · intro x hx
    rw [AddSubgroup.mem_bot.1 hx, zero_mul]
    exact Bz'.zero_mem
  · intro x hx
    rw [AddSubgroup.mem_bot.1 hx, zero_mul]
    exact Bz'.zero_mem
  · intro y _
    rw [zero_mul]
    exact Bz'.zero_mem

private theorem cellSum_minor_rightTranslate {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    {Bu Bw Bu' Bw' : AddSubgroup (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hS : IsTransversal (upperUnipotentSubgroup v Bu ⊥ Bw (forall_mul_mem_bot_mem Bu Bw))
      (upperUnipotentSubgroup v Bu' ⊥ Bw' (forall_mul_mem_bot_mem Bu' Bw')) S)
    (hfL : ∀ κ ∈ upperUnipotentSubgroup v Bu' ⊥ Bw' (forall_mul_mem_bot_mem Bu' Bw'), ∀ g, f (g * κ) = f g)
    {a c d : v.adicCompletion ℚ} (hc : ∀ u ∈ Bu, u * c ∈ Bw) (hc' : ∀ u ∈ Bu', u * c ∈ Bw') (ha : a ∈ Bu)
    (hd : d ∈ Bw) :
    cellSum v (threeCycleInv v) S (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 a c d) f)
      = cellSum v (threeCycleInv v) S f := by
  have hsplit : (upperUnipotent3 a c d : LocalGL3 v) = upperUnipotent3 0 c 0 * upperUnipotent3 a 0 d := by
    rw [upperUnipotent3_mul_upperUnipotent3]
    congr 1 <;> ring
  rw [hsplit]
  refine cellSum_rightTranslate_eq_of_conj_mul hf hS hfL (threeCycleInv_mul_upperUnipotent3_stab v c)
    (forall_mem_upperUnipotentSubgroup_iff_conj hc ?_) (forall_mem_upperUnipotentSubgroup_iff_conj hc' ?_)
    (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨ha, AddSubgroup.mem_bot.2 rfl, hd⟩)
    (forall_mem_upperUnipotentSubgroup_iff_conj ?_ ?_)
  · intro y hy
    rw [AddSubgroup.mem_bot.1 hy, mul_zero]
    exact Bw.zero_mem
  · intro y hy
    rw [AddSubgroup.mem_bot.1 hy, mul_zero]
    exact Bw'.zero_mem
  · intro u _
    rw [mul_zero]
    exact Bw'.zero_mem
  · intro y hy
    rw [AddSubgroup.mem_bot.1 hy, mul_zero]
    exact Bw'.zero_mem

private theorem cellSum_open_rightTranslate {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    {K : Subgroup (LocalGL3 v)} {Bx By Bz : AddSubgroup (v.adicCompletion ℚ)} {h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz}
    {S : Finset (LocalGL3 v)} (hS : IsTransversal K (upperUnipotentSubgroup v Bx By Bz h) S)
    (hfL : ∀ κ ∈ upperUnipotentSubgroup v Bx By Bz h, ∀ g, f (g * κ) = f g) {a b c : v.adicCompletion ℚ}
    (ht : (upperUnipotent3 a b c : LocalGL3 v) ∈ K) (hb : ∀ x ∈ Bx, x * b ∈ Bz) (ha : ∀ y ∈ By, a * y ∈ Bz)
    (w : LocalGL3 v) :
    cellSum v w S (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 a b c) f) = cellSum v w S f := by
  have h1 : (upperUnipotent3 a b c : LocalGL3 v) = 1 * upperUnipotent3 a b c := (one_mul _).symm
  rw [h1]
  refine cellSum_rightTranslate_eq_of_conj_mul hf hS hfL (w := w) (p := 0) (q := 0) (r := 0) ?_ (fun g => ?_)
    (fun g => ?_) ht (forall_mem_upperUnipotentSubgroup_iff_conj hb ha)
  · rw [mul_one, upperUnipotent3_zero, one_mul]
  · simp
  · simp

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_CellTransport

section JoinPiece_Evaluations

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "q" => (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ)
local notation "ϖ" => (uniformizerUnit ℚ v : v.adicCompletion ℚ)

private theorem residueCard_eq_residueCardC : residueCard v = residueCardC v := by
  simp only [residueCard, residueCardC, natCard_quot_eq_absNorm]

private theorem one_le_residueCard_real : (1 : ℝ) ≤ q := by
  have h : (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ≠ 0 := natCast_natCard_quot_ne_zero v
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast h)

private theorem residueCard_real_pos : (0 : ℝ) < q := lt_of_lt_of_le one_pos (one_le_residueCard_real v)

private theorem norm_eq_zpow_of_valued_eq {t : v.adicCompletion ℚ} {n : ℤ} (h : Valued.v t = WithZero.exp n) :
    ‖t‖ = q ^ n := by
  have h' := ofReal_norm_eq_of_valued_eq v (a := -n) (by rw [h, neg_neg])
  rw [zpow_neg, inv_inv] at h'
  exact Complex.ofReal_injective (by rw [h', Complex.ofReal_zpow, Complex.ofReal_natCast])

private theorem norm_le_zpow_of_valued_le {t : v.adicCompletion ℚ} {n : ℤ} (h : Valued.v t ≤ WithZero.exp n) :
    ‖t‖ ≤ q ^ n := by
  rcases eq_or_ne t 0 with rfl | ht
  · simpa using (zpow_pos (residueCard_real_pos v) n).le
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  rw [norm_eq_zpow_of_valued_eq v (WithZero.exp_log hvt).symm]
  rw [← WithZero.exp_log hvt, WithZero.exp_le_exp] at h
  exact zpow_le_zpow_right₀ (one_le_residueCard_real v) h

private theorem zpow_le_norm_of_le_valued {t : v.adicCompletion ℚ} {n : ℤ} (h : WithZero.exp n ≤ Valued.v t) :
    q ^ n ≤ ‖t‖ := by
  have hvt : Valued.v t ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.2 WithZero.exp_ne_zero) h)
  rw [norm_eq_zpow_of_valued_eq v (WithZero.exp_log hvt).symm]
  rw [← WithZero.exp_log hvt, WithZero.exp_le_exp] at h
  exact zpow_le_zpow_right₀ (one_le_residueCard_real v) h

private theorem
    norm_le_one_of_valued_le {t : v.adicCompletion ℚ} (h : Valued.v t ≤ WithZero.exp (-(0 : ℤ))) : ‖t‖ ≤ 1 := by
  simpa using norm_le_zpow_of_valued_le v h

private theorem exp_one_le_valued_of_not_le {t : v.adicCompletion ℚ} (h : ¬ Valued.v t ≤ WithZero.exp (-(0 : ℤ))) :
    WithZero.exp (1 : ℤ) ≤ Valued.v t := by
  have ht : t ≠ 0 := by rintro rfl; exact h (by simp)
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  rw [← WithZero.exp_log hvt, WithZero.exp_le_exp] at h ⊢
  omega

private theorem norm_eq_one_of_unit {t : v.adicCompletion ℚ} (h0 : Valued.v t ≤ WithZero.exp (-(0 : ℤ)))
    (h1 : ¬ Valued.v t ≤ WithZero.exp (-(1 : ℤ))) : ‖t‖ = 1 := by
  have ht : t ≠ 0 := by rintro rfl; exact h1 (by simp)
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  rw [norm_eq_zpow_of_valued_eq v (WithZero.exp_log hvt).symm]
  rw [← WithZero.exp_log hvt, neg_zero, WithZero.exp_le_exp] at h0
  rw [← WithZero.exp_log hvt, WithZero.exp_le_exp] at h1
  have : WithZero.log (Valued.v t) = 0 := by omega
  rw [this, zpow_zero]

private theorem norm_uniformizerUnit_eq : ‖ϖ‖ = q⁻¹ := by
  rw [norm_eq_zpow_of_valued_eq v (AdelicLevel.valued_uniformizerUnit (K := ℚ) (v := v)), zpow_neg_one]

private theorem norm_mul_uniformizerUnit (t : v.adicCompletion ℚ) : ‖t * ϖ‖ = ‖t‖ * q⁻¹ := by
  rw [norm_mul, norm_uniformizerUnit_eq]

private theorem norm_div_uniformizerUnit (t : v.adicCompletion ℚ) : ‖t / ϖ‖ = ‖t‖ * q := by
  rw [norm_div, norm_uniformizerUnit_eq, div_inv_eq_mul]

private theorem valued_mul_uniformizerUnit_le {t : v.adicCompletion ℚ} (h : Valued.v t ≤ WithZero.exp (-(0 : ℤ))) :
    Valued.v (t * ϖ) ≤ WithZero.exp (-(0 : ℤ)) := by
  rw [map_mul, AdelicLevel.valued_uniformizerUnit]
  calc Valued.v t * WithZero.exp (-1 : ℤ) ≤ WithZero.exp (-(0 : ℤ)) * WithZero.exp (-1 : ℤ) := by gcongr
    _ ≤ WithZero.exp (-(0 : ℤ)) := by rw [← WithZero.exp_add, WithZero.exp_le_exp]; omega

private theorem valued_div_uniformizerUnit_le {t : v.adicCompletion ℚ} (h : Valued.v t ≤ WithZero.exp (-(1 : ℤ))) :
    Valued.v (t / ϖ) ≤ WithZero.exp (-(0 : ℤ)) := by
  rw [map_div₀, AdelicLevel.valued_uniformizerUnit, div_le_iff₀ (by simp), ← WithZero.exp_add]
  simpa using h

private theorem one_le_norm_mul_uniformizerUnit {t : v.adicCompletion ℚ} (h : ¬ Valued.v t ≤ WithZero.exp (-(0 : ℤ))) :
    1 ≤ ‖t * ϖ‖ := by
  have h1 := exp_one_le_valued_of_not_le v h
  have : WithZero.exp (0 : ℤ) ≤ Valued.v (t * ϖ) := by
    rw [map_mul, AdelicLevel.valued_uniformizerUnit]
    calc WithZero.exp (0 : ℤ) = WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := by rw [← WithZero.exp_add]; norm_num
      _ ≤ Valued.v t * WithZero.exp (-1 : ℤ) := by gcongr
  simpa using zpow_le_norm_of_le_valued v this

private theorem
    one_le_norm_of_not_le {t : v.adicCompletion ℚ} (h : ¬ Valued.v t ≤ WithZero.exp (-(0 : ℤ))) : 1 ≤ ‖t‖ := by
  have h1 := zpow_le_norm_of_le_valued v (exp_one_le_valued_of_not_le v h)
  exact le_trans (by simpa using one_le_residueCard_real v) h1

private theorem not_valued_le_one_of_not_le {t : v.adicCompletion ℚ} (h : ¬ Valued.v t ≤ WithZero.exp (-(0 : ℤ))) :
    ¬ Valued.v t ≤ WithZero.exp (-(1 : ℤ)) := fun h' =>
  h (h'.trans (by rw [WithZero.exp_le_exp]; omega))

private theorem cornerCellProfile_word (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1)
    (y z : v.adicCompletion ℚ) :
    cornerCellProfile v
        (torusDifference v (firstTorusElement v)
          (torusDifference v (secondTorusElement v) (sphericalSection3 v))) y z =
      ballIndicatorAt v 0 y *
        ((residueCardC v - 1) / residueCardC v ^ 2 * ballIndicatorAt v 0 z -
          (residueCardC v - 1) * ballIndicatorAt v 1 z) := by
  have hq0 : (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ≠ 0 := natCast_natCard_quot_ne_zero v
  have hqr : (0 : ℝ) < q := residueCard_real_pos v
  have hq1 : (1 : ℝ) ≤ q := one_le_residueCard_real v
  have hq0 : q ≠ 0 := hqr.ne'
  have hϖ : ϖ ≠ 0 := (uniformizerUnit ℚ v).ne_zero
  rw [cornerCellProfile_torusDifference_first v (torusDifference_mem_principalSeries3 v _ hφ),
    cornerCellProfile_torusDifference_second v hφ, cornerCellProfile_torusDifference_second v hφ,
    div_mul_cancel₀ z hϖ, residueCard_eq_residueCardC]
  simp only [cornerCellProfile, sphericalSection3_cornerCellPoint, norm_mul_uniformizerUnit, norm_div_uniformizerUnit]
  simp only [residueCardC]
  by_cases hy : Valued.v y ≤ WithZero.exp (-(0 : ℤ))
  · rw [ballIndicatorAt_of_le v hy]
    have hy1 : max 1 ‖y‖ = 1 := max_eq_left (norm_le_one_of_valued_le v hy)
    have hyϖ : max 1 (‖y‖ * q⁻¹) = 1 := by
      rw [← norm_mul_uniformizerUnit]
      exact max_eq_left (norm_le_one_of_valued_le v (valued_mul_uniformizerUnit_le v hy))
    rw [hy1, hyϖ]
    by_cases hz : Valued.v z ≤ WithZero.exp (-(0 : ℤ))
    · rw [ballIndicatorAt_of_le v hz]
      have hz1 : max (1 : ℝ) ‖z‖ = 1 := max_eq_left (norm_le_one_of_valued_le v hz)
      have hzϖ : max (1 : ℝ) (‖z‖ * q⁻¹) = 1 := by
        rw [← norm_mul_uniformizerUnit]
        exact max_eq_left (norm_le_one_of_valued_le v (valued_mul_uniformizerUnit_le v hz))
      rw [hz1, hzϖ]
      by_cases hzb : Valued.v z ≤ WithZero.exp (-(1 : ℤ))
      · have hzd : max (1 : ℝ) (‖z‖ * q) = 1 := by
          rw [← norm_div_uniformizerUnit]
          exact max_eq_left (norm_le_one_of_valued_le v (valued_div_uniformizerUnit_le v hzb))
        rw [hzd, ballIndicatorAt_of_le v hzb]
        push_cast
        field_simp
        ring
      · have hzd : max (1 : ℝ) (‖z‖ * q) = q := by
          rw [norm_eq_one_of_unit v hz hzb, one_mul]; exact max_eq_right hq1
        rw [hzd, ballIndicatorAt_of_not_le v hzb]
        push_cast
        field_simp
        ring
    ·
      rw [ballIndicatorAt_of_not_le v hz, ballIndicatorAt_of_not_le v (not_valued_le_one_of_not_le v hz)]
      have hZ1 : (1 : ℝ) ≤ ‖z‖ := one_le_norm_of_not_le v hz
      have hZϖ : (1 : ℝ) ≤ ‖z‖ * q⁻¹ := by rw [← norm_mul_uniformizerUnit]; exact one_le_norm_mul_uniformizerUnit v hz
      have hZq : (1 : ℝ) ≤ ‖z‖ * q := le_trans hZ1 (le_mul_of_one_le_right (by positivity) hq1)
      rw [max_eq_right hZ1, max_eq_right hZϖ, max_eq_right hZq]
      have hZ0 : ‖z‖ ≠ 0 := (lt_of_lt_of_le one_pos hZ1).ne'
      push_cast
      field_simp
      ring
  ·
    rw [ballIndicatorAt_of_not_le v hy, zero_mul]
    have hY1 : (1 : ℝ) ≤ ‖y‖ := one_le_norm_of_not_le v hy
    have hYϖ : (1 : ℝ) ≤ ‖y‖ * q⁻¹ := by rw [← norm_mul_uniformizerUnit]; exact one_le_norm_mul_uniformizerUnit v hy
    have hY0 : ‖y‖ ≠ 0 := (lt_of_lt_of_le one_pos hY1).ne'
    rw [max_eq_right hY1, max_eq_right hYϖ]
    rcases le_total ‖y‖ ‖z‖ with hyz | hyz
    · have h1 : max ‖y‖ ‖z‖ = ‖z‖ := max_eq_right hyz
      have h2 : max (‖y‖ * q⁻¹) (‖z‖ * q⁻¹) = ‖z‖ * q⁻¹ := max_eq_right (by gcongr)
      have h3 : max ‖y‖ (‖z‖ * q) = ‖z‖ * q := max_eq_right (hyz.trans (le_mul_of_one_le_right (by positivity) hq1))
      have h4 : max (‖y‖ * q⁻¹) ‖z‖ = ‖z‖ :=
        max_eq_right ((mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ hq1)).trans hyz)
      have hZ0 : ‖z‖ ≠ 0 := (lt_of_lt_of_le (lt_of_lt_of_le one_pos hY1) hyz).ne'
      rw [h1, h2, h3, h4]
      push_cast
      field_simp
      ring
    · have h1 : max ‖y‖ ‖z‖ = ‖y‖ := max_eq_left hyz
      have h2 : max (‖y‖ * q⁻¹) (‖z‖ * q⁻¹) = ‖y‖ * q⁻¹ := max_eq_left (by gcongr)
      rcases le_total ‖y‖ (‖z‖ * q) with hyzq | hyzq
      · have h3 : max ‖y‖ (‖z‖ * q) = ‖z‖ * q := max_eq_right hyzq
        have h4 : max (‖y‖ * q⁻¹) ‖z‖ = ‖z‖ := max_eq_right (by rwa [← div_eq_mul_inv, div_le_iff₀ hqr])
        have hZ0 : ‖z‖ ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hyzq
          exact absurd (hyzq.trans_lt' (lt_of_lt_of_le one_pos hY1)) (lt_irrefl _)
        rw [h1, h2, h3, h4]
        push_cast
        field_simp
        ring
      · have h3 : max ‖y‖ (‖z‖ * q) = ‖y‖ := max_eq_left hyzq
        have h4 : max (‖y‖ * q⁻¹) ‖z‖ = ‖y‖ * q⁻¹ := max_eq_left (by rwa [← div_eq_mul_inv, le_div_iff₀ hqr])
        rw [h1, h2, h3, h4]
        push_cast
        field_simp
        ring

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "q" => (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ)
local notation "ϖ" => (uniformizerUnit ℚ v : v.adicCompletion ℚ)

private theorem valued_div_uniformizerUnit_le_of_le {t : v.adicCompletion ℚ} {n : ℤ}
    (h : Valued.v t ≤ WithZero.exp (-(n + 1))) : Valued.v (t / ϖ) ≤ WithZero.exp (-n) := by
  rw [map_div₀, AdelicLevel.valued_uniformizerUnit, div_le_iff₀ (by simp), ← WithZero.exp_add]
  convert h using 2
  all_goals try rfl
  ring

private theorem not_valued_le_of_not_le {t : v.adicCompletion ℚ} {m n : ℤ} (hmn : m ≤ n)
    (h : ¬ Valued.v t ≤ WithZero.exp (-m)) : ¬ Valued.v t ≤ WithZero.exp (-n) := fun h' =>
  h (h'.trans (by rw [WithZero.exp_le_exp]; omega))

private theorem exp_le_valued_of_not_le {t : v.adicCompletion ℚ} {n : ℤ} (h : ¬ Valued.v t ≤ WithZero.exp (-(n + 1))) :
    WithZero.exp (-n) ≤ Valued.v t := by
  have ht : t ≠ 0 := by rintro rfl; exact h (by simp)
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  rw [← WithZero.exp_log hvt, WithZero.exp_le_exp] at h ⊢
  omega

private theorem
    one_le_norm_of_not_le_one {t : v.adicCompletion ℚ} (h : ¬ Valued.v t ≤ WithZero.exp (-(1 : ℤ))) : 1 ≤ ‖t‖ := by
  simpa using zpow_le_norm_of_le_valued v (exp_le_valued_of_not_le v (n := 0) (by simpa using h))

private theorem one_le_norm_mul_residueCard_of_not_le_one {t : v.adicCompletion ℚ}
    (h : ¬ Valued.v t ≤ WithZero.exp (-(1 : ℤ))) : 1 ≤ ‖t‖ * q :=
  le_trans (one_le_norm_of_not_le_one v h) (le_mul_of_one_le_right (norm_nonneg _) (one_le_residueCard_real v))

private theorem
    norm_mul_residueCard_eq_one_of_shell {t : v.adicCompletion ℚ} (h1 : Valued.v t ≤ WithZero.exp (-(1 : ℤ)))
    (h2 : ¬ Valued.v t ≤ WithZero.exp (-(2 : ℤ))) : ‖t‖ * q = 1 := by
  rw [← norm_div_uniformizerUnit]
  refine norm_eq_one_of_unit v (valued_div_uniformizerUnit_le_of_le v (n := 0) (by simpa using h1)) fun h' => h2 ?_
  rw [map_div₀, AdelicLevel.valued_uniformizerUnit, div_le_iff₀ (by simp), ← WithZero.exp_add] at h'
  convert h' using 2
  all_goals try rfl

private theorem norm_le_one_of_valued_le_index {t : v.adicCompletion ℚ} {n : ℤ} (hn : 0 ≤ n)
    (h : Valued.v t ≤ WithZero.exp (-n)) : ‖t‖ ≤ 1 :=
  norm_le_one_of_valued_le v (h.trans (by rw [WithZero.exp_le_exp]; omega))

private theorem minorCellProfile_word (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1)
    (u w : v.adicCompletion ℚ) :
    minorCellProfile v
        (torusDifference v (firstTorusElement v)
          (torusDifference v (firstTorusElement v) (sphericalSection3 v))) u w =
      (1 - residueCardC v) * ((((max 1 ‖w‖)⁻¹ : ℝ) : ℂ) + residueCardC v * ballIndicatorAt v 1 w) *
          ballIndicatorAt v 1 u +
        (residueCardC v - 1) * residueCardC v *
          ((((max 1 ‖w‖)⁻¹ : ℝ) : ℂ) + (residueCardC v - 1) * ballIndicatorAt v 1 w +
            residueCardC v ^ 2 * ballIndicatorAt v 2 w) * ballIndicatorAt v 2 u := by
  have hqr : (0 : ℝ) < q := residueCard_real_pos v
  have hq1 : (1 : ℝ) ≤ q := one_le_residueCard_real v
  have hq0 : q ≠ 0 := hqr.ne'
  have hqC : ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ) ≠ 0 := natCast_natCard_quot_ne_zero v
  rw [minorCellProfile_torusDifference_first v (torusDifference_mem_principalSeries3 v _ hφ),
    minorCellProfile_torusDifference_first v hφ, minorCellProfile_torusDifference_first v hφ,
    residueCard_eq_residueCardC]
  simp only [minorCellProfile, sphericalSection3_minorCellPoint, norm_div_uniformizerUnit]
  simp only [residueCardC]
  by_cases hu1 : Valued.v u ≤ WithZero.exp (-(1 : ℤ))
  · rw [ballIndicatorAt_of_le v hu1]
    have hU1 : max (1 : ℝ) ‖u‖ = 1 := max_eq_left (norm_le_one_of_valued_le_index v (by norm_num) hu1)
    by_cases hu2 : Valued.v u ≤ WithZero.exp (-(2 : ℤ))
    ·
      rw [ballIndicatorAt_of_le v hu2]
      have hUq : max (1 : ℝ) (‖u‖ * q) = 1 := by
        rw [← norm_div_uniformizerUnit]
        exact max_eq_left (norm_le_one_of_valued_le_index v (by norm_num)
          (valued_div_uniformizerUnit_le_of_le v (n := 1) (by simpa using hu2)))
      have hUqq : max (1 : ℝ) (‖u‖ * q * q) = 1 := by
        rw [← norm_div_uniformizerUnit, ← norm_div_uniformizerUnit]
        exact max_eq_left (norm_le_one_of_valued_le v (valued_div_uniformizerUnit_le_of_le v (n := 0) (by
          simpa using valued_div_uniformizerUnit_le_of_le v (n := 1) (by simpa using hu2))))
      rw [hU1, hUq, hUqq]
      by_cases hw1 : Valued.v w ≤ WithZero.exp (-(1 : ℤ))
      · rw [ballIndicatorAt_of_le v hw1]
        have hW1 : max (1 : ℝ) ‖w‖ = 1 := max_eq_left (norm_le_one_of_valued_le_index v (by norm_num) hw1)
        by_cases hw2 : Valued.v w ≤ WithZero.exp (-(2 : ℤ))
        · rw [ballIndicatorAt_of_le v hw2]
          have hWq : max (1 : ℝ) (‖w‖ * q) = 1 := by
            rw [← norm_div_uniformizerUnit]
            exact max_eq_left (norm_le_one_of_valued_le_index v (by norm_num)
              (valued_div_uniformizerUnit_le_of_le v (n := 1) (by simpa using hw2)))
          have hWqq : max (1 : ℝ) (‖w‖ * q * q) = 1 := by
            rw [← norm_div_uniformizerUnit, ← norm_div_uniformizerUnit]
            exact max_eq_left (norm_le_one_of_valued_le v (valued_div_uniformizerUnit_le_of_le v (n := 0) (by
              simpa using valued_div_uniformizerUnit_le_of_le v (n := 1) (by simpa using hw2))))
          rw [hW1, hWq, hWqq]
          push_cast
          ring
        · rw [ballIndicatorAt_of_not_le v hw2]
          have hWq : ‖w‖ * q = 1 := norm_mul_residueCard_eq_one_of_shell v hw1 hw2
          have hWq' : max (1 : ℝ) (‖w‖ * q) = 1 := by rw [hWq, max_self]
          have hWqq : max (1 : ℝ) (‖w‖ * q * q) = q := by rw [hWq, one_mul]; exact max_eq_right hq1
          rw [hW1, hWq', hWqq]
          push_cast
          field_simp
          ring
      · rw [ballIndicatorAt_of_not_le v hw1, ballIndicatorAt_of_not_le v (not_valued_le_of_not_le v (by norm_num) hw1)]
        have hWq1 : (1 : ℝ) ≤ ‖w‖ * q := one_le_norm_mul_residueCard_of_not_le_one v hw1
        have hWqq1 : (1 : ℝ) ≤ ‖w‖ * q * q := le_trans hWq1 (le_mul_of_one_le_right (by positivity) hq1)
        have hW0 : ‖w‖ ≠ 0 := (lt_of_lt_of_le one_pos (one_le_norm_of_not_le_one v hw1)).ne'
        rw [max_eq_right hWq1, max_eq_right hWqq1, max_eq_right (one_le_norm_of_not_le_one v hw1)]
        push_cast
        field_simp
        ring
    ·
      rw [ballIndicatorAt_of_not_le v hu2]
      have hUq : ‖u‖ * q = 1 := norm_mul_residueCard_eq_one_of_shell v hu1 hu2
      have hUq' : max (1 : ℝ) (‖u‖ * q) = 1 := by rw [hUq, max_self]
      have hUqq : max (1 : ℝ) (‖u‖ * q * q) = q := by rw [hUq, one_mul]; exact max_eq_right hq1
      rw [hU1, hUq', hUqq]
      by_cases hw1 : Valued.v w ≤ WithZero.exp (-(1 : ℤ))
      · rw [ballIndicatorAt_of_le v hw1]
        have hW1 : max (1 : ℝ) ‖w‖ = 1 := max_eq_left (norm_le_one_of_valued_le_index v (by norm_num) hw1)
        have hWq : max (1 : ℝ) (‖w‖ * q) = 1 := by
          rw [← norm_div_uniformizerUnit]
          exact max_eq_left (norm_le_one_of_valued_le v (valued_div_uniformizerUnit_le_of_le v (n := 0) (by
            simpa using hw1)))
        have hWqq : max q (‖w‖ * q * q) = q := by
          refine max_eq_left ?_
          have : ‖w‖ * q ≤ 1 := by
            rw [← norm_div_uniformizerUnit]
            exact norm_le_one_of_valued_le v (valued_div_uniformizerUnit_le_of_le v (n := 0) (by simpa using hw1))
          calc ‖w‖ * q * q ≤ 1 * q := by gcongr
            _ = q := one_mul q
        rw [hW1, hWq, hWqq]
        push_cast
        field_simp
        ring
      · rw [ballIndicatorAt_of_not_le v hw1]
        have hWq1 : (1 : ℝ) ≤ ‖w‖ * q := one_le_norm_mul_residueCard_of_not_le_one v hw1
        have hWqq : max q (‖w‖ * q * q) = ‖w‖ * q * q := max_eq_right (by
          calc q = 1 * q := (one_mul q).symm
            _ ≤ ‖w‖ * q * q := by gcongr)
        have hW0 : ‖w‖ ≠ 0 := (lt_of_lt_of_le one_pos (one_le_norm_of_not_le_one v hw1)).ne'
        rw [max_eq_right hWq1, hWqq, max_eq_right (one_le_norm_of_not_le_one v hw1)]
        push_cast
        field_simp
        ring
  ·
    rw [ballIndicatorAt_of_not_le v hu1, ballIndicatorAt_of_not_le v (not_valued_le_of_not_le v (by norm_num) hu1)]
    have hU : (1 : ℝ) ≤ ‖u‖ := one_le_norm_of_not_le_one v hu1
    have hUq : (1 : ℝ) ≤ ‖u‖ * q := le_trans hU (le_mul_of_one_le_right (by positivity) hq1)
    have hUqq : (1 : ℝ) ≤ ‖u‖ * q * q := le_trans hUq (le_mul_of_one_le_right (by positivity) hq1)
    have hU0 : ‖u‖ ≠ 0 := (lt_of_lt_of_le one_pos hU).ne'
    rw [max_eq_right hU, max_eq_right hUq, max_eq_right hUqq]
    rcases le_total ‖u‖ ‖w‖ with huw | huw
    · have hW0 : ‖w‖ ≠ 0 := (lt_of_lt_of_le (lt_of_lt_of_le one_pos hU) huw).ne'
      rw [max_eq_right huw, max_eq_right (by gcongr : ‖u‖ * q ≤ ‖w‖ * q),
        max_eq_right (by gcongr : ‖u‖ * q * q ≤ ‖w‖ * q * q)]
      push_cast
      field_simp
      ring
    · rw [max_eq_left huw, max_eq_left (by gcongr : ‖w‖ * q ≤ ‖u‖ * q),
        max_eq_left (by gcongr : ‖w‖ * q * q ≤ ‖u‖ * q * q)]
      push_cast
      field_simp
      ring

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "q" => (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ)
local notation "ϖ" => (uniformizerUnit ℚ v : v.adicCompletion ℚ)

private noncomputable def cornerBracket (j : ℤ) (z : v.adicCompletion ℚ) : ℂ :=
  (residueCardC v - 1) ^ 2 * ballIndicatorAt v (j + 1) z +
    (1 - residueCardC v) * (ballIndicatorAt v j z - ballIndicatorAt v (j + 1) z)

private theorem sum_cornerBracket_eq_zero {kz j : ℤ} {N : ℕ} (hkj : kz ≤ j) (hjN : j + 1 ≤ N)
    {Z : Finset (v.adicCompletion ℚ)}
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-kz) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) (c : ℂ) :
    ∑ z ∈ Z, c * cornerBracket v j z = 0 := by
  simp only [cornerBracket]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_ballIndicatorAt_of_representatives v (by omega) hjN hZ',
    sum_ballIndicatorAt_of_representatives v hkj (by omega) hZ']
  have hsucc : ((N : ℤ) - j).toNat = ((N : ℤ) - (j + 1)).toNat + 1 := by omega
  rw [hsucc, pow_succ]
  ring

private theorem ballIndicatorAt_mul_uniformizerUnit (i : ℤ) (z : v.adicCompletion ℚ) :
    ballIndicatorAt v i (z * ϖ) = ballIndicatorAt v (i - 1) z := by
  have key : Valued.v (z * ϖ) ≤ WithZero.exp (-i) ↔ Valued.v z ≤ WithZero.exp (-(i - 1)) := by
    rw [map_mul, AdelicLevel.valued_uniformizerUnit, show (-(i - 1) : ℤ) = -i + 1 by ring, WithZero.exp_add,
      ← le_div_iff₀ (by simp), div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
    norm_num
  by_cases h : Valued.v z ≤ WithZero.exp (-(i - 1))
  · rw [ballIndicatorAt_of_le v (key.2 h), ballIndicatorAt_of_le v h]
  · rw [ballIndicatorAt_of_not_le v (fun h' => h (key.1 h')), ballIndicatorAt_of_not_le v h]

private theorem cornerBracket_mul_uniformizerUnit (j : ℤ) (z : v.adicCompletion ℚ) :
    cornerBracket v j (z * ϖ) = cornerBracket v (j - 1) z := by
  simp only [cornerBracket, ballIndicatorAt_mul_uniformizerUnit, add_sub_cancel_right, sub_add_cancel]

private theorem exists_max_one_norm_eq_zpow {ky : ℤ} (hky : ky ≤ 0) {y : v.adicCompletion ℚ}
    (hy : Valued.v y ≤ WithZero.exp (-ky)) : ∃ a : ℤ, 0 ≤ a ∧ a ≤ -ky ∧ max (1 : ℝ) ‖y‖ = q ^ a := by
  by_cases hy0 : Valued.v y ≤ WithZero.exp (-(0 : ℤ))
  · exact ⟨0, le_rfl, by omega, by rw [zpow_zero]; exact max_eq_left (norm_le_one_of_valued_le v hy0)⟩
  · have hy' : y ≠ 0 := by rintro rfl; exact hy0 (by simp)
    have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy'
    refine ⟨WithZero.log (Valued.v y), ?_, ?_, ?_⟩
    · rw [← WithZero.exp_log hvy, neg_zero, WithZero.exp_le_exp] at hy0; omega
    · rw [← WithZero.exp_log hvy, WithZero.exp_le_exp] at hy; exact hy
    · rw [norm_eq_zpow_of_valued_eq v (WithZero.exp_log hvy).symm]
      refine max_eq_right ?_
      rw [← WithZero.exp_log hvy, neg_zero, WithZero.exp_le_exp] at hy0
      calc (1 : ℝ) = q ^ (0 : ℤ) := (zpow_zero _).symm
        _ ≤ q ^ WithZero.log (Valued.v y) := zpow_le_zpow_right₀ (one_le_residueCard_real v) (by omega)

private theorem
    cornerCellProfile_word11 (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1) {ky : ℤ} (hky : ky ≤ 0)
    {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ WithZero.exp (-ky)) :
    ∃ (c : ℂ) (j : ℤ), ky + 1 ≤ j ∧ j ≤ 1 ∧ ∀ z : v.adicCompletion ℚ,
      cornerCellProfile v
          (torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v)))
          y z = c * cornerBracket v j z := by
  have hqr : (0 : ℝ) < q := residueCard_real_pos v
  have hq1 : (1 : ℝ) ≤ q := one_le_residueCard_real v
  obtain ⟨a, ha0, hay, hm⟩ := exists_max_one_norm_eq_zpow v hky hy
  have hqa : (0 : ℝ) < q ^ a := zpow_pos hqr a
  have hqC : ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ) ≠ 0 := natCast_natCard_quot_ne_zero v
  have hqaC : ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ) ^ a ≠ 0 := zpow_ne_zero a hqC
  have hqa1 : q ^ (a - 1) * q = q ^ a := by rw [← zpow_add_one₀ hqr.ne']; congr 1; ring
  have hqa2 : q ^ (a - 2) * q = q ^ (a - 1) := by rw [← zpow_add_one₀ hqr.ne']; congr 1; ring
  have hle1 : q ^ (a - 1) ≤ q ^ a := zpow_le_zpow_right₀ hq1 (by omega)
  have hle2 : q ^ (a - 2) ≤ q ^ (a - 1) := zpow_le_zpow_right₀ hq1 (by omega)
  refine ⟨(((q ^ a * q ^ a)⁻¹ : ℝ) : ℂ), 1 - a, by omega, by omega, fun z => ?_⟩
  rw [cornerCellProfile_torusDifference_first v (torusDifference_mem_principalSeries3 v _ hφ),
    cornerCellProfile_torusDifference_first v hφ, cornerCellProfile_torusDifference_first v hφ,
    residueCard_eq_residueCardC]
  simp only [cornerCellProfile, sphericalSection3_cornerCellPoint, norm_div_uniformizerUnit, hm]
  simp only [cornerBracket, residueCardC, show (1 - a + 1 : ℤ) = 2 - a by ring]
  by_cases hz2 : Valued.v z ≤ WithZero.exp (-(2 - a))
  ·
    have hz1 : Valued.v z ≤ WithZero.exp (-(1 - a)) := hz2.trans (by rw [WithZero.exp_le_exp]; omega)
    rw [ballIndicatorAt_of_le v hz2, ballIndicatorAt_of_le v hz1]
    have hZ : ‖z‖ ≤ q ^ (a - 2) := by
      have := norm_le_zpow_of_valued_le v hz2; rwa [show (-(2 - a) : ℤ) = a - 2 by ring] at this
    have h1 : max (q ^ a) ‖z‖ = q ^ a := max_eq_left (hZ.trans (hle2.trans hle1))
    have h2 : max (q ^ a) (‖z‖ * q) = q ^ a := max_eq_left (by
      calc ‖z‖ * q ≤ q ^ (a - 2) * q := by gcongr
        _ = q ^ (a - 1) := hqa2
        _ ≤ q ^ a := hle1)
    have h3 : max (q ^ a) (‖z‖ * q * q) = q ^ a := max_eq_left (by
      calc ‖z‖ * q * q ≤ q ^ (a - 2) * q * q := by gcongr
        _ = q ^ a := by rw [hqa2, hqa1])
    rw [h1, h2, h3]
    push_cast
    field_simp
    ring
  · by_cases hz1 : Valued.v z ≤ WithZero.exp (-(1 - a))
    ·
      rw [ballIndicatorAt_of_not_le v hz2, ballIndicatorAt_of_le v hz1]
      have hz0 : z ≠ 0 := by rintro rfl; exact hz2 (by simp)
      have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
      have hZ : ‖z‖ = q ^ (a - 1) := by
        rw [norm_eq_zpow_of_valued_eq v (WithZero.exp_log hvz).symm]
        rw [← WithZero.exp_log hvz, WithZero.exp_le_exp] at hz1 hz2
        congr 1
        omega
      have h1 : max (q ^ a) ‖z‖ = q ^ a := max_eq_left (hZ ▸ hle1)
      have h2 : max (q ^ a) (‖z‖ * q) = q ^ a := by rw [hZ, hqa1, max_self]
      have h3 : max (q ^ a) (‖z‖ * q * q) = q ^ a * q := by
        rw [hZ, hqa1]; exact max_eq_right (le_mul_of_one_le_right hqa.le hq1)
      rw [h1, h2, h3]
      push_cast
      field_simp
      ring
    ·
      rw [ballIndicatorAt_of_not_le v hz2, ballIndicatorAt_of_not_le v hz1]
      have hZ : q ^ a ≤ ‖z‖ := by
        have h := exp_le_valued_of_not_le v (n := -a) (by rwa [show (-(-a + 1) : ℤ) = -(1 - a) by ring])
        have := zpow_le_norm_of_le_valued v h; rwa [neg_neg] at this
      have hz0 : ‖z‖ ≠ 0 := (lt_of_lt_of_le hqa hZ).ne'
      have h1 : max (q ^ a) ‖z‖ = ‖z‖ := max_eq_right hZ
      have h2 : max (q ^ a) (‖z‖ * q) = ‖z‖ * q := max_eq_right (hZ.trans (le_mul_of_one_le_right (norm_nonneg _) hq1))
      have h3 : max (q ^ a) (‖z‖ * q * q) = ‖z‖ * q * q :=
        max_eq_right (hZ.trans (le_mul_of_one_le_right (norm_nonneg _) hq1 |>.trans
          (le_mul_of_one_le_right (by positivity) hq1)))
      rw [h1, h2, h3]
      push_cast
      field_simp
      ring

end LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "ϖ" => (uniformizerUnit ℚ v : v.adicCompletion ℚ)

private theorem
    valued_mul_uniformizerUnit_le_of_le {t : v.adicCompletion ℚ} {k : ℤ} (h : Valued.v t ≤ WithZero.exp (-k)) :
    Valued.v (t * ϖ) ≤ WithZero.exp (-k) := by
  rw [map_mul, AdelicLevel.valued_uniformizerUnit]
  calc Valued.v t * WithZero.exp (-1 : ℤ) ≤ WithZero.exp (-k) * WithZero.exp (-1 : ℤ) := by gcongr
    _ ≤ WithZero.exp (-k) := by rw [← WithZero.exp_add, WithZero.exp_le_exp]; omega

private theorem sum_sum_cornerCellProfile_word11_eq_zero (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1)
    {ky kz : ℤ} (hky : ky ≤ 0) (hkzy : kz ≤ ky) {N : ℕ} (hN : 2 ≤ N) {Y Z : Finset (v.adicCompletion ℚ)}
    (hY : ∀ r ∈ Y, Valued.v r ≤ WithZero.exp (-ky))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-kz) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ y ∈ Y, ∑ z ∈ Z, cornerCellProfile v
      (torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v))) y z
      = 0 := by
  refine Finset.sum_eq_zero fun y hy => ?_
  obtain ⟨c, j, hj₁, hj₂, hz⟩ := cornerCellProfile_word11 v hφ hky (hY y hy)
  rw [Finset.sum_congr rfl fun z _ => hz z]
  exact sum_cornerBracket_eq_zero v (by omega) (by omega) hZ' c

private theorem sum_sum_cornerCellProfile_word211_eq_zero (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1)
    {ky kz : ℤ} (hky : ky ≤ 0) (hkzy : kz ≤ ky) {N : ℕ} (hN : 2 ≤ N) {Y Z : Finset (v.adicCompletion ℚ)}
    (hY : ∀ r ∈ Y, Valued.v r ≤ WithZero.exp (-ky))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-kz) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ y ∈ Y, ∑ z ∈ Z, cornerCellProfile v
      (torusDifference v (secondTorusElement v)
        (torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v)))) y z
      = 0 := by
  have hmem := torusDifference_mem_principalSeries3 v (firstTorusElement v)
    (torusDifference_mem_principalSeries3 v (firstTorusElement v) hφ)
  refine Finset.sum_eq_zero fun y hy => ?_
  obtain ⟨c, j, hj₁, hj₂, hz⟩ := cornerCellProfile_word11 v hφ hky (hY y hy)
  obtain ⟨c', j', hj'₁, hj'₂, hz'⟩ :=
    cornerCellProfile_word11 v hφ hky (valued_mul_uniformizerUnit_le_of_le v (hY y hy))
  have hterm : ∀ z ∈ Z, cornerCellProfile v (torusDifference v (secondTorusElement v)
      (torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v)))) y z =
      c * cornerBracket v j z - (residueCard v)⁻¹ ^ 2 * (c' * cornerBracket v (j' - 1) z) := by
    intro z _
    rw [cornerCellProfile_torusDifference_second v hmem, hz z, hz' (z * ϖ), cornerBracket_mul_uniformizerUnit]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sum_cornerBracket_eq_zero v (by omega) (by omega) hZ' c,
    ← Finset.mul_sum, sum_cornerBracket_eq_zero v (by omega) (by omega) hZ' c', mul_zero, sub_zero]

private theorem sum_sum_eq_zero_of_minor_shape {ku kw : ℤ} (hku : ku ≤ 0) (hkw : kw ≤ 0) {N : ℕ} (hN : 2 ≤ N)
    {U W : Finset (v.adicCompletion ℚ)}
    (hU' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ku) →
      ∃! r, r ∈ U ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    (hW' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-kw) →
      ∃! r, r ∈ W ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    (hq : residueCardC v ≠ 0) {F : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ} {ρ ρ' : v.adicCompletion ℚ → ℂ}
    (hF : ∀ u ∈ U, ∀ w ∈ W, F u w =
      ((1 - residueCardC v) * (ρ w + residueCardC v * ballIndicatorAt v 1 w) * ballIndicatorAt v 1 u +
        (residueCardC v - 1) * residueCardC v *
          (ρ w + (residueCardC v - 1) * ballIndicatorAt v 1 w + residueCardC v ^ 2 * ballIndicatorAt v 2 w) *
            ballIndicatorAt v 2 u) -
      (residueCardC v)⁻¹ *
        ((1 - residueCardC v) * (ρ' w + residueCardC v * ballIndicatorAt v 0 w) * ballIndicatorAt v 1 u +
          (residueCardC v - 1) * residueCardC v *
            (ρ' w + (residueCardC v - 1) * ballIndicatorAt v 0 w + residueCardC v ^ 2 * ballIndicatorAt v 1 w) *
              ballIndicatorAt v 2 u)) :
    ∑ w ∈ W, ∑ u ∈ U, F u w = 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hU1 : ∑ u ∈ U, ballIndicatorAt v 1 u = residueCardC v ^ (M + 1) := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hU']; congr 1; omega
  have hU2 : ∑ u ∈ U, ballIndicatorAt v 2 u = residueCardC v ^ M := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hU']; congr 1; omega
  have hW0 : ∑ w ∈ W, ballIndicatorAt v 0 w = residueCardC v ^ (M + 2) := by
    rw [sum_ballIndicatorAt_of_representatives v hkw (by push_cast; linarith) hW']; congr 1
  have hW1 : ∑ w ∈ W, ballIndicatorAt v 1 w = residueCardC v ^ (M + 1) := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hW']; congr 1; omega
  have hW2 : ∑ w ∈ W, ballIndicatorAt v 2 w = residueCardC v ^ M := by
    rw [sum_ballIndicatorAt_of_representatives v (by omega) (by push_cast; linarith) hW']; congr 1; omega
  have hinner : ∀ w ∈ W, ∑ u ∈ U, F u w = (residueCardC v - 1) * residueCardC v ^ (M + 1) *
      ((-ballIndicatorAt v 1 w + residueCardC v ^ 2 * ballIndicatorAt v 2 w) -
        (residueCardC v)⁻¹ * (-ballIndicatorAt v 0 w + residueCardC v ^ 2 * ballIndicatorAt v 1 w)) := by
    intro w hw
    rw [Finset.sum_congr rfl fun u hu => hF u hu w hw]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hU1, hU2]
    ring
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hW0, hW1, hW2]
  field_simp
  ring

private theorem sum_sum_minorCellProfile_word211_eq_zero (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1)
    {ku kw : ℤ} (hku : ku ≤ 0) (hkw : kw ≤ 0) {N : ℕ} (hN : 2 ≤ N) {U W : Finset (v.adicCompletion ℚ)}
    (hU' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-ku) →
      ∃! r, r ∈ U ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    (hW' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-kw) →
      ∃! r, r ∈ W ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ w ∈ W, ∑ u ∈ U, minorCellProfile v
      (torusDifference v (secondTorusElement v)
        (torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v)))) u w
      = 0 := by
  have hmem := torusDifference_mem_principalSeries3 v (firstTorusElement v)
    (torusDifference_mem_principalSeries3 v (firstTorusElement v) hφ)
  have hq : residueCardC v ≠ 0 := natCast_natCard_quot_ne_zero v
  refine sum_sum_eq_zero_of_minor_shape v hku hkw hN hU' hW' hq
    (ρ := fun w => (((max 1 ‖w‖)⁻¹ : ℝ) : ℂ)) (ρ' := fun w => (((max 1 ‖w * ϖ‖)⁻¹ : ℝ) : ℂ)) fun u _ w _ => ?_
  rw [minorCellProfile_torusDifference_second v hmem, minorCellProfile_word v hφ, minorCellProfile_word v hφ,
    residueCard_eq_residueCardC, ballIndicatorAt_mul_uniformizerUnit, ballIndicatorAt_mul_uniformizerUnit]
  norm_num

end LanglandsTunnell.CubicInduction

end JoinPiece_Evaluations

section JoinPiece_OpenValueFurniture

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem one_lt_natCard_real : (1 : ℝ) < (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) := by
  exact_mod_cast one_lt_natCard_quot v

private theorem natCard_real_pos : (0 : ℝ) < (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) :=
  zero_lt_one.trans (one_lt_natCard_real v)

private theorem norm_eq_inv_zpow_of_valued_eq {t : v.adicCompletion ℚ} {s : ℤ}
    (h : Valued.v t = WithZero.exp (-s)) : ‖t‖ = ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ s)⁻¹ := by
  apply Complex.ofReal_injective
  rw [ofReal_norm_eq_of_valued_eq v h]
  simp only [Complex.ofReal_inv, Complex.ofReal_zpow, Complex.ofReal_natCast]

private theorem norm_le_zpow_of_mem_ball {z : v.adicCompletion ℚ} {a : ℤ}
    (h : Valued.v z ≤ WithZero.exp (-(-a))) : ‖z‖ ≤ (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a := by
  obtain ⟨t, -, ht⟩ := exists_valued_eq_exp v (-(-a))
  have hle : ‖z‖ ≤ ‖t‖ := Valued.toNormedField.norm_le_iff.mpr (by rw [ht]; exact h)
  rwa [norm_eq_inv_zpow_of_valued_eq v ht, zpow_neg, inv_inv] at hle

private theorem norm_add_le_max_of_valued (a b : v.adicCompletion ℚ) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  rcases le_total (Valued.v a) (Valued.v b) with hab | hab
  · have h : Valued.v (a + b) ≤ Valued.v b := (Valuation.map_add _ a b).trans (max_eq_right hab).le
    exact (Valued.toNormedField.norm_le_iff.mpr h).trans (le_max_right _ _)
  · have h : Valued.v (a + b) ≤ Valued.v a := (Valuation.map_add _ a b).trans (max_eq_left hab).le
    exact (Valued.toNormedField.norm_le_iff.mpr h).trans (le_max_left _ _)

private theorem max_norm_eq_of_norm_sub_le {M : ℝ} {a b : v.adicCompletion ℚ} (h : ‖a - b‖ ≤ M) :
    max M ‖a‖ = max M ‖b‖ := by
  have key : ∀ {a b : v.adicCompletion ℚ}, ‖a - b‖ ≤ M → max M ‖a‖ ≤ max M ‖b‖ := by
    intro a b hab
    refine max_le (le_max_left _ _) ?_
    have h1 : ‖a‖ ≤ max ‖b‖ ‖a - b‖ := by
      have h2 := norm_add_le_max_of_valued v b (a - b)
      rwa [add_sub_cancel] at h2
    rcases le_total ‖b‖ ‖a - b‖ with hb | hb
    · rw [max_eq_right hb] at h1
      exact le_max_of_le_left (h1.trans hab)
    · rw [max_eq_left hb] at h1
      exact le_max_of_le_right h1
  have h' : ‖b - a‖ ≤ M := by rwa [norm_sub_rev]
  exact le_antisymm (key h) (key h')

private theorem norm_sub_le_one_of_valued_le {a b : v.adicCompletion ℚ}
    (h : Valued.v (a - b) ≤ WithZero.exp (-(0 : ℤ))) : ‖a - b‖ ≤ 1 := by
  rw [neg_zero, WithZero.exp_zero] at h
  exact Valued.toNormedField.norm_le_one_iff.mpr h

private theorem sum_sub_eq_sum_of_representatives {k : ℤ} {N : ℕ} {Z : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-k))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    {c : v.adicCompletion ℚ} (hc : Valued.v c ≤ WithZero.exp (-k))
    {g : v.adicCompletion ℚ → ℂ} (hg : ∀ a b, Valued.v (a - b) ≤ WithZero.exp (-(N : ℤ)) → g a = g b) :
    ∑ z ∈ Z, g (z - c) = ∑ z ∈ Z, g z := by
  classical
  have himg : ∑ z ∈ Z.image (fun z => z - c), g z = ∑ z ∈ Z, g (z - c) :=
    Finset.sum_image (by
      intro x _ y _ hxy
      exact sub_left_inj.mp hxy)
  rw [← himg]
  have hW : ∀ r ∈ Z.image (fun z => z - c), Valued.v r ≤ WithZero.exp (-k) := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    exact (Valuation.map_sub _ z c).trans (max_le (hZ z hz) hc)
  have hW' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z.image (fun z => z - c) ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)) := by
    intro x hx
    have hxc : Valued.v (x + c) ≤ WithZero.exp (-k) := (Valuation.map_add _ x c).trans (max_le hx hc)
    obtain ⟨r, ⟨hrZ, hr⟩, huniq⟩ := hZ' (x + c) hxc
    refine ⟨r - c, ⟨Finset.mem_image.mpr ⟨r, hrZ, rfl⟩, ?_⟩, ?_⟩
    · rwa [sub_sub_eq_add_sub]
    · rintro s ⟨hs, hxs⟩
      obtain ⟨r', hr'Z, rfl⟩ := Finset.mem_image.mp hs
      rw [sub_sub_eq_add_sub] at hxs
      rw [huniq r' ⟨hr'Z, hxs⟩]
  exact sum_eq_sum_of_ball_representatives v hg hW hW' hZ hZ'

private theorem sphericalOpenProfile_eq_of_integral_sub (y : v.adicCompletion ℚ) {x x' z z' : v.adicCompletion ℚ}
    (hx : Valued.v (x - x') ≤ WithZero.exp (-(0 : ℤ))) (hz : Valued.v (z - z') ≤ WithZero.exp (-(0 : ℤ))) :
    (max (max (1 : ℝ) ‖y‖) ‖z - y * x‖ * max (max (1 : ℝ) ‖x‖) ‖z‖)⁻¹ =
      (max (max (1 : ℝ) ‖y‖) ‖z' - y * x'‖ * max (max (1 : ℝ) ‖x'‖) ‖z'‖)⁻¹ := by
  have hx1 : ‖x - x'‖ ≤ 1 := norm_sub_le_one_of_valued_le v hx
  have hz1 : ‖z - z'‖ ≤ 1 := norm_sub_le_one_of_valued_le v hz
  have hfirst : max (max (1 : ℝ) ‖y‖) ‖z - y * x‖ = max (max (1 : ℝ) ‖y‖) ‖z' - y * x'‖ := by
    apply max_norm_eq_of_norm_sub_le v
    have hsplit : z - y * x - (z' - y * x') = (z - z') + (-y) * (x - x') := by ring
    rw [hsplit]
    refine (norm_add_le_max_of_valued v _ _).trans (max_le ?_ ?_)
    · exact hz1.trans (le_max_left _ _)
    · rw [norm_mul, norm_neg]
      calc ‖y‖ * ‖x - x'‖ ≤ ‖y‖ * 1 := mul_le_mul_of_nonneg_left hx1 (norm_nonneg _)
        _ = ‖y‖ := mul_one _
        _ ≤ max 1 ‖y‖ := le_max_right _ _
  have hxx : max (1 : ℝ) ‖x‖ = max (1 : ℝ) ‖x'‖ := max_norm_eq_of_norm_sub_le v hx1
  have hsecond : max (max (1 : ℝ) ‖x‖) ‖z‖ = max (max (1 : ℝ) ‖x'‖) ‖z'‖ := by
    rw [hxx]
    exact max_norm_eq_of_norm_sub_le v (hz1.trans (le_max_left _ _))
  rw [hfirst, hsecond]

private theorem filter_representatives {j i : ℤ} {N : ℕ} (hji : j ≤ i) (hiN : i ≤ (N : ℤ))
    {Z : Finset (v.adicCompletion ℚ)}
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    [DecidablePred fun r : v.adicCompletion ℚ => Valued.v r ≤ WithZero.exp (-i)] :
    ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-i) →
      ∃! r, r ∈ Z.filter (fun r => Valued.v r ≤ WithZero.exp (-i)) ∧
        Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)) := by
  intro x hx
  have hxj : Valued.v x ≤ WithZero.exp (-j) := hx.trans (WithZero.exp_le_exp.mpr (by omega))
  obtain ⟨r, ⟨hrZ, hr⟩, huniq⟩ := hZ' x hxj
  have hrj : Valued.v r ≤ WithZero.exp (-i) := by
    have h : Valued.v (x - (x - r)) ≤ max (Valued.v x) (Valued.v (x - r)) := Valuation.map_sub _ x (x - r)
    rw [sub_sub_cancel] at h
    refine h.trans (max_le hx (hr.trans (WithZero.exp_le_exp.mpr (by omega))))
  refine ⟨r, ⟨Finset.mem_filter.mpr ⟨hrZ, hrj⟩, hr⟩, ?_⟩
  rintro s ⟨hs, hxs⟩
  exact huniq s ⟨(Finset.mem_filter.mp hs).1, hxs⟩

private theorem valued_eq_exp_of_le_of_not_le {z : v.adicCompletion ℚ} {j : ℤ} (h₁ : Valued.v z ≤ WithZero.exp (-j))
    (h₂ : ¬ Valued.v z ≤ WithZero.exp (-(j + 1))) : Valued.v z = WithZero.exp (-j) := by
  have h0 : Valued.v z ≠ 0 := fun h => h₂ (by rw [h]; exact zero_le')
  obtain ⟨L, hL⟩ : ∃ L : ℤ, Valued.v z = WithZero.exp L := ⟨_, (WithZero.exp_log h0).symm⟩
  rw [hL, WithZero.exp_le_exp] at h₁ h₂
  rw [hL]
  congr 1
  omega

private theorem inv_max_of_valued_le {a : ℤ} {z : v.adicCompletion ℚ} (hz : Valued.v z ≤ WithZero.exp (-(-a))) :
    (((max ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a) ‖z‖)⁻¹ : ℝ) : ℂ) = (residueCardC v ^ a)⁻¹ := by
  rw [max_eq_left (norm_le_zpow_of_mem_ball v hz)]
  simp only [residueCardC, Complex.ofReal_inv, Complex.ofReal_zpow, Complex.ofReal_natCast]

private theorem inv_max_of_valued_eq {a j : ℤ} (hja : j + 1 ≤ -a) {z : v.adicCompletion ℚ}
    (hz : Valued.v z = WithZero.exp (-j)) :
    (((max ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a) ‖z‖)⁻¹ : ℝ) : ℂ) = residueCardC v ^ j := by
  rw [norm_eq_inv_zpow_of_valued_eq v hz, ← zpow_neg,
    max_eq_right (zpow_le_zpow_right₀ (one_lt_natCard_real v).le (by omega)), ← zpow_neg, neg_neg]
  simp only [residueCardC, Complex.ofReal_zpow, Complex.ofReal_natCast]

private theorem sum_ballIndicatorAt_eq_zpow {j i : ℤ} {N : ℕ} (hji : j ≤ i) (hiN : i ≤ (N : ℤ))
    {Z : Finset (v.adicCompletion ℚ)}
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ r ∈ Z, ballIndicatorAt v i r = residueCardC v ^ ((N : ℤ) - i) := by
  rw [sum_ballIndicatorAt_of_representatives v hji hiN hZ', ← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.mpr hiN)]

private theorem sum_inv_max_zpow_norm_aux {a : ℤ} (ha : 0 ≤ a) (n : ℕ) :
    ∀ {N : ℕ} {Z : Finset (v.adicCompletion ℚ)},
      (∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-(-a - n))) →
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(-a - n)) →
        ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) →
      ∑ z ∈ Z, (((max ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a) ‖z‖)⁻¹ : ℝ) : ℂ) =
        residueCardC v ^ N * (1 + (n : ℂ) * (1 - (residueCardC v)⁻¹)) := by
  have hq : residueCardC v ≠ 0 := natCast_natCard_quot_ne_zero v
  induction n with
  | zero =>
    intro N Z hZ hZ'
    simp only [Nat.cast_zero, sub_zero, zero_mul, add_zero, mul_one] at hZ hZ' ⊢
    have hcount := sum_ballIndicatorAt_eq_zpow v (le_refl (-a)) (by omega) hZ'
    rw [Finset.sum_congr rfl fun z hz => inv_max_of_valued_le v (hZ z hz), Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun r hr => ballIndicatorAt_of_le v (hZ r hr), Finset.sum_const, nsmul_eq_mul,
      mul_one] at hcount
    rw [hcount, sub_neg_eq_add, zpow_add₀ hq, zpow_natCast, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero a hq), mul_one]
  | succ n ih =>
    intro N Z hZ hZ'
    classical
    set j : ℤ := -a - ((n + 1 : ℕ) : ℤ) with hj_def
    have hj1 : j + 1 = -a - (n : ℤ) := by rw [hj_def]; push_cast; ring
    have hj1N : j + 1 ≤ (N : ℤ) := by omega

    have hinner := filter_representatives v (by omega : j ≤ j + 1) hj1N hZ'
    have hZf : ∀ r ∈ Z.filter (fun r => Valued.v r ≤ WithZero.exp (-(j + 1))),
        Valued.v r ≤ WithZero.exp (-(-a - (n : ℤ))) := by
      intro r hr
      rw [← hj1]
      exact (Finset.mem_filter.mp hr).2
    have hZf' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(-a - (n : ℤ))) →
        ∃! r, r ∈ Z.filter (fun r => Valued.v r ≤ WithZero.exp (-(j + 1))) ∧
          Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)) := by
      intro x hx
      rw [← hj1] at hx
      exact hinner x hx
    have hIH := ih hZf hZf'

    have hsplit : ∑ z ∈ Z, (((max ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a) ‖z‖)⁻¹ : ℝ) : ℂ) =
        ∑ z ∈ Z.filter (fun r => Valued.v r ≤ WithZero.exp (-(j + 1))),
            (((max ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a) ‖z‖)⁻¹ : ℝ) : ℂ) +
          residueCardC v ^ j * ∑ z ∈ Z, (ballIndicatorAt v j z - ballIndicatorAt v (j + 1) z) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z hz => ?_
      have hzj : Valued.v z ≤ WithZero.exp (-j) := hZ z hz
      rw [ballIndicatorAt_of_le v hzj]
      by_cases hz1 : Valued.v z ≤ WithZero.exp (-(j + 1))
      · rw [if_pos hz1, ballIndicatorAt_of_le v hz1, sub_self, mul_zero, add_zero]
      · rw [if_neg hz1, ballIndicatorAt_of_not_le v hz1, sub_zero, mul_one, zero_add,
          inv_max_of_valued_eq v (by omega) (valued_eq_exp_of_le_of_not_le v hzj hz1)]
    rw [hsplit, hIH, Finset.sum_sub_distrib, sum_ballIndicatorAt_eq_zpow v (le_refl j) (by omega) hZ',
      sum_ballIndicatorAt_eq_zpow v (by omega) hj1N hZ']
    have h1 : residueCardC v ^ ((N : ℤ) - j) = residueCardC v ^ (N : ℕ) / residueCardC v ^ j := by
      rw [zpow_sub₀ hq, zpow_natCast]
    have h2 : residueCardC v ^ ((N : ℤ) - (j + 1)) =
        residueCardC v ^ (N : ℕ) / residueCardC v ^ j / residueCardC v := by
      rw [show (N : ℤ) - (j + 1) = (N : ℤ) - j - 1 by ring, zpow_sub₀ hq, zpow_sub₀ hq, zpow_one, zpow_natCast]
    rw [h1, h2]
    have hqj : residueCardC v ^ j ≠ 0 := zpow_ne_zero j hq
    push_cast
    field_simp
    ring

private theorem sum_inv_max_zpow_norm {a j : ℤ} (ha : 0 ≤ a) (hja : j ≤ -a) {N : ℕ} {Z : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ z ∈ Z, (((max ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a) ‖z‖)⁻¹ : ℝ) : ℂ) =
      residueCardC v ^ N * (1 + ((-a - j : ℤ) : ℂ) * (1 - (residueCardC v)⁻¹)) := by
  have hn : j = -a - ((-a - j).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [hn] at hZ hZ'
  have hcast : (((-a - j).toNat : ℕ) : ℂ) = ((-a - j : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [sum_inv_max_zpow_norm_aux v ha (-a - j).toNat hZ hZ', hcast]

private theorem sum_ballIndicatorAt_mul_inv_max_zpow_norm {a i j : ℤ} (ha : 0 ≤ a) (hji : j ≤ i) (hia : i ≤ -a)
    {N : ℕ} {Z : Finset (v.adicCompletion ℚ)}
    (_hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ x ∈ Z, ballIndicatorAt v i x * (((max ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a) ‖x‖)⁻¹ : ℝ) : ℂ) =
      residueCardC v ^ N * (1 + ((-a - i : ℤ) : ℂ) * (1 - (residueCardC v)⁻¹)) := by
  classical
  have hiN : i ≤ (N : ℤ) := by omega
  have hsys := filter_representatives v hji hiN hZ'
  have hsub : ∀ r ∈ Z.filter (fun r => Valued.v r ≤ WithZero.exp (-i)), Valued.v r ≤ WithZero.exp (-i) :=
    fun r hr => (Finset.mem_filter.mp hr).2
  rw [← sum_inv_max_zpow_norm v ha hia hsub hsys, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : Valued.v z ≤ WithZero.exp (-i)
  · rw [if_pos hz, ballIndicatorAt_of_le v hz, one_mul]
  · rw [if_neg hz, ballIndicatorAt_of_not_le v hz, zero_mul]

private theorem sum_eq_residueCardC_mul_sum_of_representatives_succ {k : ℤ} {N : ℕ} (hkN : k ≤ (N : ℤ))
    {Z Z₁ : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-k))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ₁ : ∀ r ∈ Z₁, Valued.v r ≤ WithZero.exp (-k))
    (hZ₁' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z₁ ∧ Valued.v (x - r) ≤ WithZero.exp (-((N + 1 : ℕ) : ℤ)))
    {g : v.adicCompletion ℚ → ℂ} (hg : ∀ a b, Valued.v (a - b) ≤ WithZero.exp (-(N : ℤ)) → g a = g b) :
    ∑ z ∈ Z₁, g z = residueCardC v * ∑ z ∈ Z, g z := by
  simp only [residueCardC]
  obtain ⟨Y, hY, hY', hYcard⟩ := exists_finset_ball_representatives v (N : ℤ) ((N : ℤ) + 1) (by omega)
  obtain ⟨W, hW, hW', -, hWsum⟩ := exists_ball_representatives_add v hkN hZ hZ' hY hY'
  have hg' : ∀ a b, Valued.v (a - b) ≤ WithZero.exp (-((N : ℤ) + 1)) → g a = g b :=
    fun a b h => hg a b (h.trans (WithZero.exp_le_exp.mpr (by omega)))
  have hZ₁'' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z₁ ∧ Valued.v (x - r) ≤ WithZero.exp (-((N : ℤ) + 1)) := by
    push_cast at hZ₁'
    exact hZ₁'
  rw [sum_eq_sum_of_ball_representatives v hg' hZ₁ hZ₁'' hW hW', hWsum g]
  have hinner : ∀ r ∈ Z, ∑ s ∈ Y, g (r + s) = (Y.card : ℂ) * g r := by
    intro r _
    rw [Finset.sum_congr rfl fun s hs => hg (r + s) r (by rw [show r + s - r = s by ring]; exact hY s hs),
      Finset.sum_const, nsmul_eq_mul]
  have h1 : ((N : ℤ) + 1 - (N : ℤ)).toNat = 1 := by omega
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, hYcard, h1, pow_one]

private theorem valued_div_uniformizerUnit (z : v.adicCompletion ℚ) :
    Valued.v (z / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) = Valued.v z * WithZero.exp 1 := by
  rw [map_div₀, valued_uniformizerUnit, div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]

private theorem valued_uniformizerUnit_mul (x : v.adicCompletion ℚ) :
    Valued.v ((uniformizerUnit ℚ v : v.adicCompletion ℚ) * x) = Valued.v x * WithZero.exp (-1) := by
  rw [map_mul, valued_uniformizerUnit, mul_comm]

private theorem mul_exp_le_exp {u : WithZero (Multiplicative ℤ)} {m c : ℤ} (h : u ≤ WithZero.exp (-m)) :
    u * WithZero.exp c ≤ WithZero.exp (-(m - c)) := by
  calc u * WithZero.exp c ≤ WithZero.exp (-m) * WithZero.exp c := mul_le_mul_left h _
    _ = WithZero.exp (-(m - c)) := by rw [← WithZero.exp_add]; congr 1; ring

private theorem sum_div_uniformizerUnit_eq_inv_mul_sum {k : ℤ} {N : ℕ} (hkN : k ≤ (N : ℤ))
    {Z Zm : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-k))
    (hZ' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-((N + 1 : ℕ) : ℤ)))
    (hZm : ∀ r ∈ Zm, Valued.v r ≤ WithZero.exp (-(k - 1)))
    (hZm' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(k - 1)) →
      ∃! r, r ∈ Zm ∧ Valued.v (x - r) ≤ WithZero.exp (-((N + 1 : ℕ) : ℤ)))
    {g : v.adicCompletion ℚ → ℂ} (hg : ∀ a b, Valued.v (a - b) ≤ WithZero.exp (-(N : ℤ)) → g a = g b) :
    ∑ z ∈ Z, g (z / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) = (residueCardC v)⁻¹ * ∑ z ∈ Zm, g z := by
  classical
  have hq : residueCardC v ≠ 0 := natCast_natCard_quot_ne_zero v
  have hϖ : (uniformizerUnit ℚ v : v.adicCompletion ℚ) ≠ 0 := Units.ne_zero _
  have hZ'' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-((N : ℤ) + 1)) := by
    push_cast at hZ'
    exact hZ'
  set Zi : Finset (v.adicCompletion ℚ) := Z.image (fun z => z / (uniformizerUnit ℚ v : v.adicCompletion ℚ))
    with hZi_def
  have himg : ∑ z ∈ Zi, g z = ∑ z ∈ Z, g (z / (uniformizerUnit ℚ v : v.adicCompletion ℚ)) :=
    Finset.sum_image (by
      intro x _ y _ hxy
      exact (div_left_inj' hϖ).mp hxy)

  have hZi : ∀ r ∈ Zi, Valued.v r ≤ WithZero.exp (-(k - 1)) := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    rw [valued_div_uniformizerUnit]
    exact mul_exp_le_exp (hZ z hz)

  have hZi' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(k - 1)) →
      ∃! r, r ∈ Zi ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ)) := by
    intro x hx
    have hxk : Valued.v ((uniformizerUnit ℚ v : v.adicCompletion ℚ) * x) ≤ WithZero.exp (-k) := by
      rw [valued_uniformizerUnit_mul]
      have h := mul_exp_le_exp (c := -1) hx
      rwa [show k - 1 - -1 = k by ring] at h
    obtain ⟨r, ⟨hrZ, hr⟩, huniq⟩ := hZ'' ((uniformizerUnit ℚ v : v.adicCompletion ℚ) * x) hxk
    have hdiv : ∀ w : v.adicCompletion ℚ,
        x - w / (uniformizerUnit ℚ v : v.adicCompletion ℚ) =
          ((uniformizerUnit ℚ v : v.adicCompletion ℚ) * x - w) / (uniformizerUnit ℚ v : v.adicCompletion ℚ) := by
      intro w
      field_simp
    refine ⟨r / (uniformizerUnit ℚ v : v.adicCompletion ℚ), ⟨Finset.mem_image.mpr ⟨r, hrZ, rfl⟩, ?_⟩, ?_⟩
    · rw [hdiv, valued_div_uniformizerUnit]
      have h := mul_exp_le_exp (c := 1) hr
      rwa [show (N : ℤ) + 1 - 1 = (N : ℤ) by ring] at h
    · rintro s ⟨hs, hxs⟩
      obtain ⟨r', hr'Z, rfl⟩ := Finset.mem_image.mp hs
      rw [hdiv, valued_div_uniformizerUnit] at hxs
      have hxs' : Valued.v ((uniformizerUnit ℚ v : v.adicCompletion ℚ) * x - r') ≤
          WithZero.exp (-((N : ℤ) + 1)) := by
        have h := mul_exp_le_exp (c := -1) hxs
        rw [show (N : ℤ) - -1 = (N : ℤ) + 1 by ring] at h
        rwa [mul_assoc, ← WithZero.exp_add, show (1 : ℤ) + -1 = 0 by norm_num, WithZero.exp_zero, mul_one] at h
      rw [huniq r' ⟨hr'Z, hxs'⟩]
  have hrefine := sum_eq_residueCardC_mul_sum_of_representatives_succ v (by omega) hZi hZi' hZm hZm' hg
  rw [← himg, hrefine, inv_mul_cancel_left₀ hq]

end LanglandsTunnell.CubicInduction

end JoinPiece_OpenValueFurniture

section JoinPiece_OpenValueH4

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "q" => (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ)
local notation "Q" => ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ)

private noncomputable def sphericalOpenValue (x y z : v.adicCompletion ℚ) : ℂ :=
  (((max (max 1 ‖y‖) ‖z - y * x‖ * max (max 1 ‖x‖) ‖z‖)⁻¹ : ℝ) : ℂ)

private theorem one_lt_q : (1 : ℝ) < q := by exact_mod_cast one_lt_natCard_quot v

private theorem Q_ne_zero : Q ≠ 0 := natCast_natCard_quot_ne_zero v

private theorem valued_sub_eq_right_of_lt {s t : v.adicCompletion ℚ} (h : Valued.v s < Valued.v t) :
    Valued.v (s - t) = Valued.v t := by
  apply le_antisymm
  · exact (Valuation.map_sub _ _ _).trans (max_le h.le le_rfl)
  · have h1 : Valued.v t ≤ max (Valued.v (s - t)) (Valued.v s) := by
      have h2 := Valuation.map_sub Valued.v (s - t) s
      rwa [sub_sub_cancel_left, Valuation.map_neg] at h2
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

private theorem norm_sub_eq_of_valued_lt {s t : v.adicCompletion ℚ} (h : Valued.v s < Valued.v t) :
    ‖s - t‖ = ‖t‖ := by
  have hvt : Valued.v t ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' h)
  rw [norm_eq_zpow_of_valued_eq v (t := s - t) (n := WithZero.log (Valued.v t))
      (by rw [valued_sub_eq_right_of_lt v h, WithZero.exp_log hvt]),
    norm_eq_zpow_of_valued_eq v (WithZero.exp_log hvt).symm]

private theorem max_zpow_norm_eq_of_valued_sub_le {e : ℤ} {s t : v.adicCompletion ℚ}
    (h : Valued.v (s - t) ≤ WithZero.exp e) : max (q ^ e) ‖s‖ = max (q ^ e) ‖t‖ := by
  have key : ∀ s t : v.adicCompletion ℚ, Valued.v (s - t) ≤ WithZero.exp e →
      max (q ^ e) ‖s‖ ≤ max (q ^ e) ‖t‖ := by
    intro s t hst
    refine max_le (le_max_left _ _) ?_
    by_cases hs : Valued.v s ≤ WithZero.exp e
    · exact (norm_le_zpow_of_valued_le v hs).trans (le_max_left _ _)
    · have h1 := norm_sub_eq_of_valued_lt v (lt_of_le_of_lt hst (not_le.1 hs))
      rw [sub_sub_cancel_left, norm_neg] at h1
      rw [← h1]
      exact le_max_right _ _
  refine le_antisymm (key s t h) (key t s ?_)
  rwa [← Valuation.map_neg, neg_sub]

private theorem valued_eq_of_mem_shell {j : ℤ} {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ WithZero.exp (-j))
    (ht' : ¬ Valued.v t ≤ WithZero.exp (-(j + 1))) : Valued.v t = WithZero.exp (-j) := by
  have ht0 : t ≠ 0 := by rintro rfl; exact ht' (by simp)
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht0
  rw [← WithZero.exp_log hvt, WithZero.exp_le_exp] at ht ht'
  rw [← WithZero.exp_log hvt]
  congr 1
  omega

private theorem valued_eq_exp_of_max_norm_eq {a : ℤ} (ha : 0 < a) {y : v.adicCompletion ℚ}
    (hy : max (1 : ℝ) ‖y‖ = q ^ a) : Valued.v y = WithZero.exp a := by
  have hqa : (1 : ℝ) < q ^ a := one_lt_zpow₀ (one_lt_q v) ha
  have hy' : ‖y‖ = q ^ a := by
    rcases max_choice (1 : ℝ) ‖y‖ with h | h <;> rw [h] at hy
    · exact absurd hy hqa.ne
    · exact hy
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy'; linarith
  have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  rw [norm_eq_zpow_of_valued_eq v (WithZero.exp_log hvy).symm] at hy'
  rw [← WithZero.exp_log hvy, zpow_right_injective₀ (residueCard_real_pos v) (one_lt_q v).ne' hy']

private theorem valued_le_one_of_max_norm_eq {y : v.adicCompletion ℚ} (hy : max (1 : ℝ) ‖y‖ = q ^ (0 : ℤ)) :
    Valued.v y ≤ WithZero.exp (-(0 : ℤ)) := by
  rw [zpow_zero] at hy
  have h3 : ‖y‖ ≤ 1 := max_eq_left_iff.1 hy
  by_contra h
  have h2 : q ^ (1 : ℤ) ≤ ‖y‖ := zpow_le_norm_of_le_valued v (exp_one_le_valued_of_not_le v h)
  rw [zpow_one] at h2
  linarith [one_lt_q v]

private theorem ballIndicatorAt_mul_ballIndicatorAt_of_le {i i' : ℤ} (h : i ≤ i') (t : v.adicCompletion ℚ) :
    ballIndicatorAt v i t * ballIndicatorAt v i' t = ballIndicatorAt v i' t := by
  by_cases ht : Valued.v t ≤ WithZero.exp (-i')
  · rw [ballIndicatorAt_of_le v ht, ballIndicatorAt_of_le v (ht.trans (WithZero.exp_le_exp.2 (by omega))), one_mul]
  · rw [ballIndicatorAt_of_not_le v ht, mul_zero]

private theorem ballIndicatorAt_sub_of_le {i : ℤ} {c : v.adicCompletion ℚ} (hc : Valued.v c ≤ WithZero.exp (-i))
    (t : v.adicCompletion ℚ) : ballIndicatorAt v i (t - c) = ballIndicatorAt v i t := by
  by_cases ht : Valued.v t ≤ WithZero.exp (-i)
  · rw [ballIndicatorAt_of_le v ht, ballIndicatorAt_of_le v ((Valuation.map_sub _ _ _).trans (max_le ht hc))]
  · rw [ballIndicatorAt_of_not_le v ht, ballIndicatorAt_of_not_le v]
    intro h
    apply ht
    have h2 : Valued.v ((t - c) + c) ≤ max (Valued.v (t - c)) (Valued.v c) := Valuation.map_add _ _ _
    rw [sub_add_cancel] at h2
    exact h2.trans (max_le h hc)

private theorem count_sub_box_eq_zpow {k i : ℤ} {N : ℕ} (hki : k ≤ i) (hiN : i ≤ (N : ℤ))
    {X : Finset (v.adicCompletion ℚ)}
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ r ∈ X, ballIndicatorAt v i r = Q ^ ((N : ℤ) - i) := by
  rw [sum_ballIndicatorAt_of_representatives v hki hiN hX', ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

private theorem card_system_eq_zpow {k : ℤ} {N : ℕ} (hkN : k ≤ (N : ℤ)) {X : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ r ∈ X, (1 : ℂ) = Q ^ ((N : ℤ) - k) := by
  rw [← count_sub_box_eq_zpow v le_rfl hkN hX']
  exact Finset.sum_congr rfl fun r hr => (ballIndicatorAt_of_le v (hX r hr)).symm

private theorem sphericalOpenValue_eq_of_max_eq {a j : ℤ} {y : v.adicCompletion ℚ}
    (hy : max (1 : ℝ) ‖y‖ = q ^ a) {x z : v.adicCompletion ℚ} (h : max (max (1 : ℝ) ‖x‖) ‖z‖ = q ^ (-j)) :
    sphericalOpenValue v x y z =
      (((q ^ (-j))⁻¹ : ℝ) : ℂ) * (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) := by
  rw [sphericalOpenValue, hy, h, mul_inv, Complex.ofReal_mul, mul_comm]

private theorem max_eq_of_norm_x_eq {j : ℤ} (hj : j ≤ 0) {x z : v.adicCompletion ℚ} (hx : ‖x‖ = q ^ (-j))
    (hz : ‖z‖ ≤ q ^ (-j)) : max (max (1 : ℝ) ‖x‖) ‖z‖ = q ^ (-j) := by
  have h1 : (1 : ℝ) ≤ q ^ (-j) := by
    simpa using zpow_le_zpow_right₀ (one_le_residueCard_real v) (show (0 : ℤ) ≤ -j by omega)
  rw [hx, max_eq_right h1, max_eq_left hz]

private theorem max_eq_of_norm_z_eq {j : ℤ} (hj : j ≤ 0) {x z : v.adicCompletion ℚ} (hx : ‖x‖ ≤ q ^ (-j))
    (hz : ‖z‖ = q ^ (-j)) : max (max (1 : ℝ) ‖x‖) ‖z‖ = q ^ (-j) := by
  have h1 : (1 : ℝ) ≤ q ^ (-j) := by
    simpa using zpow_le_zpow_right₀ (one_le_residueCard_real v) (show (0 : ℤ) ≤ -j by omega)
  rw [hz, max_eq_right (max_le h1 hx)]

private theorem coupled_const {a : ℤ} (ha : 0 ≤ a) (N : ℕ) :
    ∀ s t : v.adicCompletion ℚ, Valued.v (s - t) ≤ WithZero.exp (-(N : ℤ)) →
      (((max (q ^ a) ‖s‖)⁻¹ : ℝ) : ℂ) = (((max (q ^ a) ‖t‖)⁻¹ : ℝ) : ℂ) := by
  intro s t hst
  rw [max_zpow_norm_eq_of_valued_sub_le v (hst.trans (WithZero.exp_le_exp.2 (by omega)))]

private theorem indicator_const {i : ℤ} {N : ℕ} (hiN : i ≤ (N : ℤ)) :
    ∀ s t : v.adicCompletion ℚ, Valued.v (s - t) ≤ WithZero.exp (-(N : ℤ)) →
      ballIndicatorAt v i s = ballIndicatorAt v i t := by
  intro s t hst
  have h := ballIndicatorAt_sub_of_le v (i := i) (c := s - t) (hst.trans (WithZero.exp_le_exp.2 (by omega))) s
  rw [sub_sub_cancel] at h
  exact h.symm

private theorem inner_sum_shell_x_of_small {j : ℤ} (hj : j + 1 ≤ 0) {N : ℕ} {y : v.adicCompletion ℚ}
    (hy : max (1 : ℝ) ‖y‖ = q ^ (0 : ℤ)) {Z : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-j)) (hx' : ¬ Valued.v x ≤ WithZero.exp (-(j + 1))) :
    ∑ z ∈ Z, sphericalOpenValue v x y z =
      (((q ^ (-j))⁻¹ : ℝ) : ℂ) * (residueCardC v ^ N * (1 + ((-(0 : ℤ) - j : ℤ) : ℂ) * (1 - (residueCardC v)⁻¹))) := by
  have hxn : ‖x‖ = q ^ (-j) := norm_eq_zpow_of_valued_eq v (valued_eq_of_mem_shell v hx hx')
  have hc : Valued.v (y * x) ≤ WithZero.exp (-j) := by
    rw [Valuation.map_mul]
    calc Valued.v y * Valued.v x ≤ WithZero.exp (-(0 : ℤ)) * WithZero.exp (-j) :=
          mul_le_mul' (valued_le_one_of_max_norm_eq v hy) hx
      _ = WithZero.exp (-j) := by rw [← WithZero.exp_add]; congr 1; omega
  rw [Finset.sum_congr rfl fun z hz => sphericalOpenValue_eq_of_max_eq v hy
        (max_eq_of_norm_x_eq v (by omega) hxn (norm_le_zpow_of_valued_le v (hZ z hz))),
    ← Finset.mul_sum]
  congr 1
  rw [sum_sub_eq_sum_of_representatives v hZ hZ' hc (coupled_const v le_rfl N),
    sum_inv_max_zpow_norm v le_rfl (by omega) hZ hZ']

private theorem inner_sum_shell_x_of_large {a j : ℤ} (ha : 0 < a) (hja : j + a + 1 ≤ 0) {N : ℕ}
    {y : v.adicCompletion ℚ} (hy : max (1 : ℝ) ‖y‖ = q ^ a) {Z : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-j)) (hx' : ¬ Valued.v x ≤ WithZero.exp (-(j + 1))) :
    ∑ z ∈ Z, sphericalOpenValue v x y z =
      (((q ^ (-j))⁻¹ : ℝ) : ℂ) * (Q ^ ((N : ℤ) - j) * (((q ^ (a - j))⁻¹ : ℝ) : ℂ)) := by
  have hxv := valued_eq_of_mem_shell v hx hx'
  have hxn : ‖x‖ = q ^ (-j) := norm_eq_zpow_of_valued_eq v hxv
  have hyx : Valued.v (y * x) = WithZero.exp (a - j) := by
    rw [Valuation.map_mul, valued_eq_exp_of_max_norm_eq v ha hy, hxv, ← WithZero.exp_add, sub_eq_add_neg]
  have hdist : ∀ z ∈ Z, (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) = (((q ^ (a - j))⁻¹ : ℝ) : ℂ) := by
    intro z hz
    have hlt : Valued.v z < Valued.v (y * x) := by
      rw [hyx]; exact lt_of_le_of_lt (hZ z hz) (WithZero.exp_lt_exp.2 (by omega))
    rw [norm_sub_eq_of_valued_lt v hlt, norm_eq_zpow_of_valued_eq v hyx,
      max_eq_right (zpow_le_zpow_right₀ (one_le_residueCard_real v) (by omega))]
  rw [Finset.sum_congr rfl fun z hz => sphericalOpenValue_eq_of_max_eq v hy
        (max_eq_of_norm_x_eq v (by omega) hxn (norm_le_zpow_of_valued_le v (hZ z hz))),
    ← Finset.mul_sum, Finset.sum_congr rfl hdist, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Z.card : ℂ) = Q ^ ((N : ℤ) - j) := by
    rw [← card_system_eq_zpow v (by omega) hZ hZ', Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard]

private theorem inner_sum_shell_z {a j : ℤ} (hj : j + 1 ≤ 0) {y : v.adicCompletion ℚ} (hy : max (1 : ℝ) ‖y‖ = q ^ a)
    {Z : Finset (v.adicCompletion ℚ)} (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-(j + 1))) :
    ∑ z ∈ Z, (1 - ballIndicatorAt v (j + 1) z) * sphericalOpenValue v x y z =
      (((q ^ (-j))⁻¹ : ℝ) : ℂ) *
        (∑ z ∈ Z, (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) -
          ∑ z ∈ Z, ballIndicatorAt v (j + 1) z * (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ)) := by
  have hxn : ‖x‖ ≤ q ^ (-j) :=
    (norm_le_zpow_of_valued_le v hx).trans (zpow_le_zpow_right₀ (one_le_residueCard_real v) (by omega))
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  by_cases hz' : Valued.v z ≤ WithZero.exp (-(j + 1))
  · rw [ballIndicatorAt_of_le v hz']; ring
  · have hzn : ‖z‖ = q ^ (-j) := norm_eq_zpow_of_valued_eq v (valued_eq_of_mem_shell v (hZ z hz) hz')
    rw [ballIndicatorAt_of_not_le v hz',
      sphericalOpenValue_eq_of_max_eq v hy (max_eq_of_norm_z_eq v (by omega) hxn hzn)]
    ring

private theorem W_of_small {j : ℤ} (hj : j + 1 ≤ 0) {N : ℕ} {y : v.adicCompletion ℚ}
    (hy : max (1 : ℝ) ‖y‖ = q ^ (0 : ℤ)) {Z : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-(j + 1))) :
    ∑ z ∈ Z, (((max (q ^ (0 : ℤ)) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) -
        ∑ z ∈ Z, ballIndicatorAt v (j + 1) z * (((max (q ^ (0 : ℤ)) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) =
      residueCardC v ^ N * (1 - (residueCardC v)⁻¹) := by
  have hc1 : Valued.v (y * x) ≤ WithZero.exp (-(j + 1)) := by
    rw [Valuation.map_mul]
    calc Valued.v y * Valued.v x ≤ WithZero.exp (-(0 : ℤ)) * WithZero.exp (-(j + 1)) :=
          mul_le_mul' (valued_le_one_of_max_norm_eq v hy) hx
      _ = WithZero.exp (-(j + 1)) := by rw [← WithZero.exp_add]; congr 1; omega
  have hc : Valued.v (y * x) ≤ WithZero.exp (-j) := hc1.trans (WithZero.exp_le_exp.2 (by omega))

  rw [sum_sub_eq_sum_of_representatives v hZ hZ' hc (coupled_const v le_rfl N),
    sum_inv_max_zpow_norm v le_rfl (by omega) hZ hZ']

  have hshift : ∀ z, ballIndicatorAt v (j + 1) z * (((max (q ^ (0 : ℤ)) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) =
      (fun t => ballIndicatorAt v (j + 1) t * (((max (q ^ (0 : ℤ)) ‖t‖)⁻¹ : ℝ) : ℂ)) (z - y * x) := by
    intro z; simp only [ballIndicatorAt_sub_of_le v hc1]
  rw [Finset.sum_congr rfl fun z _ => hshift z,
    sum_sub_eq_sum_of_representatives v hZ hZ' hc
      (g := fun t => ballIndicatorAt v (j + 1) t * (((max (q ^ (0 : ℤ)) ‖t‖)⁻¹ : ℝ) : ℂ)) (fun s t hst => by
      simp only [indicator_const v (i := j + 1) (N := N) (by omega) s t hst,
        coupled_const v (a := 0) le_rfl N s t hst]),
    sum_ballIndicatorAt_mul_inv_max_zpow_norm v le_rfl (by omega : j ≤ j + 1) (by omega) hZ hZ']
  push_cast
  ring

private theorem W_of_large {a j : ℤ} (ha : 0 < a) (hja : j + a + 1 ≤ 0) {N : ℕ} {y : v.adicCompletion ℚ}
    (hy : max (1 : ℝ) ‖y‖ = q ^ a) {Z : Finset (v.adicCompletion ℚ)}
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-(j + 1))) :
    ∑ z ∈ Z, (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) -
        ∑ z ∈ Z, ballIndicatorAt v (j + 1) z * (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) =
      residueCardC v ^ N * (1 - (residueCardC v)⁻¹) * ballIndicatorAt v (j + a + 1) x +
        residueCardC v ^ N * (1 - (residueCardC v)⁻¹) * ((1 - a - j : ℤ) : ℂ) *
          (ballIndicatorAt v (j + a) x - ballIndicatorAt v (j + a + 1) x) +
        Q ^ ((N : ℤ) - j) * (1 - Q⁻¹) * (((q ^ a)⁻¹ : ℝ) : ℂ) *
          ((((max (q ^ (-(j + a))) ‖x‖)⁻¹ : ℝ) : ℂ) - (((q ^ (a + j)) : ℝ) : ℂ) * ballIndicatorAt v (j + a) x) := by
  have hyv := valued_eq_exp_of_max_norm_eq v ha hy
  have hsubQ : ∑ z ∈ Z, ballIndicatorAt v (j + 1) z = Q ^ ((N : ℤ) - (j + 1)) :=
    count_sub_box_eq_zpow v (by omega) (by omega) hZ'
  by_cases h1 : Valued.v x ≤ WithZero.exp (-(j + a + 1))
  ·
    have hc1 : Valued.v (y * x) ≤ WithZero.exp (-(j + 1)) := by
      rw [Valuation.map_mul, hyv]
      calc WithZero.exp a * Valued.v x ≤ WithZero.exp a * WithZero.exp (-(j + a + 1)) := mul_le_mul_right h1 _
        _ = WithZero.exp (-(j + 1)) := by rw [← WithZero.exp_add]; congr 1; omega
    have hc : Valued.v (y * x) ≤ WithZero.exp (-j) := hc1.trans (WithZero.exp_le_exp.2 (by omega))
    have hxn : ‖x‖ ≤ q ^ (-(j + a + 1)) := norm_le_zpow_of_valued_le v h1
    have hmax : max (q ^ (-(j + a))) ‖x‖ = q ^ (-(j + a)) :=
      max_eq_left (hxn.trans (zpow_le_zpow_right₀ (one_le_residueCard_real v) (by omega)))
    have hshift : ∀ z, ballIndicatorAt v (j + 1) z * (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) =
        (fun t => ballIndicatorAt v (j + 1) t * (((max (q ^ a) ‖t‖)⁻¹ : ℝ) : ℂ)) (z - y * x) := by
      intro z; simp only [ballIndicatorAt_sub_of_le v hc1]
    rw [ballIndicatorAt_of_le v h1, ballIndicatorAt_of_le v (h1.trans (WithZero.exp_le_exp.2 (by omega))),
      hmax,
      sum_sub_eq_sum_of_representatives v hZ hZ' hc (coupled_const v ha.le N),
      sum_inv_max_zpow_norm v ha.le (by omega) hZ hZ', Finset.sum_congr rfl fun z _ => hshift z,
      sum_sub_eq_sum_of_representatives v hZ hZ' hc
        (g := fun t => ballIndicatorAt v (j + 1) t * (((max (q ^ a) ‖t‖)⁻¹ : ℝ) : ℂ)) (fun s t hst => by
        simp only [indicator_const v (i := j + 1) (N := N) (by omega) s t hst, coupled_const v ha.le N s t hst]),
      sum_ballIndicatorAt_mul_inv_max_zpow_norm v ha.le (by omega : j ≤ j + 1) (by omega) hZ hZ']
    have hzq : (((q ^ (-(j + a)))⁻¹ : ℝ) : ℂ) - (((q ^ (a + j)) : ℝ) : ℂ) * 1 = 0 := by
      rw [mul_one, ← Complex.ofReal_sub, ← zpow_neg, neg_neg, show a + j = j + a by ring, sub_self,
        Complex.ofReal_zero]
    rw [hzq]
    push_cast
    ring
  by_cases h2 : Valued.v x ≤ WithZero.exp (-(j + a))
  ·
    have hxv : Valued.v x = WithZero.exp (-(j + a)) := valued_eq_of_mem_shell v h2 h1
    have hcv : Valued.v (y * x) = WithZero.exp (-j) := by
      rw [Valuation.map_mul, hyv, hxv, ← WithZero.exp_add]; congr 1; omega
    have hxn : ‖x‖ = q ^ (-(j + a)) := norm_eq_zpow_of_valued_eq v hxv
    have hmax : max (q ^ (-(j + a))) ‖x‖ = q ^ (-(j + a)) := by rw [hxn, max_self]
    have hconst : ∀ z ∈ Z, ballIndicatorAt v (j + 1) z * (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) =
        ballIndicatorAt v (j + 1) z * (((q ^ (-j))⁻¹ : ℝ) : ℂ) := by
      intro z _
      by_cases hz : Valued.v z ≤ WithZero.exp (-(j + 1))
      · have hlt : Valued.v z < Valued.v (y * x) := by
          rw [hcv]; exact lt_of_le_of_lt hz (WithZero.exp_lt_exp.2 (by omega))
        rw [norm_sub_eq_of_valued_lt v hlt, norm_eq_zpow_of_valued_eq v hcv,
          max_eq_right (zpow_le_zpow_right₀ (one_le_residueCard_real v) (by omega))]
      · rw [ballIndicatorAt_of_not_le v hz, zero_mul, zero_mul]
    rw [ballIndicatorAt_of_not_le v h1, ballIndicatorAt_of_le v h2, hmax,
      sum_sub_eq_sum_of_representatives v hZ hZ' hcv.le (coupled_const v ha.le N),
      sum_inv_max_zpow_norm v ha.le (by omega) hZ hZ', Finset.sum_congr rfl hconst, ← Finset.sum_mul, hsubQ]
    have hzq : (((q ^ (-(j + a)))⁻¹ : ℝ) : ℂ) - (((q ^ (a + j)) : ℝ) : ℂ) * 1 = 0 := by
      rw [mul_one, ← Complex.ofReal_sub, ← zpow_neg, neg_neg, show a + j = j + a by ring, sub_self,
        Complex.ofReal_zero]
    rw [hzq]
    have hQ : Q ≠ 0 := Q_ne_zero v
    have hQj : Q ^ j ≠ 0 := zpow_ne_zero _ hQ
    simp only [Complex.ofReal_inv, Complex.ofReal_zpow, Complex.ofReal_natCast, residueCardC, zpow_neg, inv_inv,
      zpow_sub₀ hQ, zpow_add₀ hQ, zpow_natCast, zpow_one]
    push_cast
    field_simp
    ring
  ·
    have hx0 : x ≠ 0 := by rintro rfl; exact h2 (by simp)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hbig : q ^ (-(j + a)) < ‖x‖ := by
      have h3 := zpow_le_norm_of_le_valued v (n := -(j + a) + 1) (by
        have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
        rw [← WithZero.exp_log hvx, WithZero.exp_le_exp]
        rw [← WithZero.exp_log hvx, WithZero.exp_le_exp] at h2
        omega)
      calc q ^ (-(j + a)) < q ^ (-(j + a) + 1) := zpow_lt_zpow_right₀ (one_lt_q v) (by omega)
        _ ≤ ‖x‖ := h3
    have hmax : max (q ^ (-(j + a))) ‖x‖ = ‖x‖ := max_eq_right hbig.le
    have hone : (1 : ℝ) ≤ ‖x‖ := by
      refine le_trans ?_ hbig.le
      simpa using zpow_le_zpow_right₀ (one_le_residueCard_real v) (show (0 : ℤ) ≤ -(j + a) by omega)
    have hdist : ∀ z ∈ Z, (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) =
        (((q ^ a)⁻¹ : ℝ) : ℂ) * ((‖x‖⁻¹ : ℝ) : ℂ) := by
      intro z hz
      have hlt : Valued.v z < Valued.v (y * x) := by
        rw [Valuation.map_mul, hyv]
        refine lt_of_le_of_lt (hZ z hz) ?_
        have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
        rw [← WithZero.exp_log hvx, ← WithZero.exp_add, WithZero.exp_lt_exp]
        rw [← WithZero.exp_log hvx, WithZero.exp_le_exp] at h2
        omega
      have hyn : ‖y‖ = q ^ a := by
        rw [norm_eq_zpow_of_valued_eq v hyv]
      rw [norm_sub_eq_of_valued_lt v hlt, norm_mul, hyn,
        max_eq_right (le_mul_of_one_le_right (zpow_pos (residueCard_real_pos v) a).le hone), mul_inv,
        Complex.ofReal_mul]
    have hsum2 : ∑ z ∈ Z, ballIndicatorAt v (j + 1) z * (((max (q ^ a) ‖z - y * x‖)⁻¹ : ℝ) : ℂ) =
        Q ^ ((N : ℤ) - (j + 1)) * ((((q ^ a)⁻¹ : ℝ) : ℂ) * ((‖x‖⁻¹ : ℝ) : ℂ)) := by
      rw [Finset.sum_congr rfl fun z hz => congrArg (ballIndicatorAt v (j + 1) z * ·) (hdist z hz)]
      show (∑ z ∈ Z, ballIndicatorAt v (j + 1) z * ((((q ^ a)⁻¹ : ℝ) : ℂ) * ((‖x‖⁻¹ : ℝ) : ℂ))) = _
      rw [← Finset.sum_mul, hsubQ]
    rw [ballIndicatorAt_of_not_le v h1, ballIndicatorAt_of_not_le v h2, hmax, Finset.sum_congr rfl hdist, hsum2,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : (Z.card : ℂ) = Q ^ ((N : ℤ) - j) := by
      rw [← card_system_eq_zpow v (by omega) hZ hZ', Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard]
    have hQ : Q ≠ 0 := Q_ne_zero v
    have hQj : Q ^ j ≠ 0 := zpow_ne_zero _ hQ
    simp only [Complex.ofReal_inv, Complex.ofReal_zpow, Complex.ofReal_natCast, residueCardC,
      zpow_sub₀ hQ, zpow_add₀ hQ, zpow_natCast, zpow_one]
    push_cast
    field_simp
    ring

private theorem arm1_eq {j : ℤ} {N : ℕ} (hjN : j + 1 ≤ (N : ℤ)) {X : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-j))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-j) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {F : v.adicCompletion ℚ → ℂ} {T : ℂ} (hT : ∀ x ∈ X, ¬ Valued.v x ≤ WithZero.exp (-(j + 1)) → F x = T) :
    ∑ x ∈ X, (1 - ballIndicatorAt v (j + 1) x) * F x = (Q ^ ((N : ℤ) - j) - Q ^ ((N : ℤ) - (j + 1))) * T := by
  rw [← card_system_eq_zpow v (by omega) hX hX', ← count_sub_box_eq_zpow v (by omega) hjN hX',
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases hx' : Valued.v x ≤ WithZero.exp (-(j + 1))
  · rw [ballIndicatorAt_of_le v hx']; ring
  · rw [hT x hx hx']

private theorem sum_sum_lShell_sphericalOpenValue {a j : ℤ} (ha : 0 ≤ a) (hja : j + a + 1 ≤ 0) {N : ℕ}
    {y : v.adicCompletion ℚ} (hy : max (1 : ℝ) ‖y‖ = (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ a)
    {X Z : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-j))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-j) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-j))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-j) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ x ∈ X, ∑ z ∈ Z, (1 - ballIndicatorAt v (j + 1) x * ballIndicatorAt v (j + 1) z) * sphericalOpenValue v x y z =
      residueCardC v ^ (2 * N) * (1 - (residueCardC v)⁻¹) / residueCardC v ^ a *
        (1 + (residueCardC v)⁻¹ - (j : ℂ) * (1 - (residueCardC v)⁻¹)) := by
  have hQ : Q ≠ 0 := Q_ne_zero v
  have hQj : Q ^ j ≠ 0 := zpow_ne_zero _ hQ
  have hQa : Q ^ a ≠ 0 := zpow_ne_zero _ hQ
  have hsplit : ∀ x ∈ X, ∑ z ∈ Z, (1 - ballIndicatorAt v (j + 1) x * ballIndicatorAt v (j + 1) z) *
        sphericalOpenValue v x y z =
      (1 - ballIndicatorAt v (j + 1) x) * ∑ z ∈ Z, sphericalOpenValue v x y z +
        ballIndicatorAt v (j + 1) x * ∑ z ∈ Z, (1 - ballIndicatorAt v (j + 1) z) * sphericalOpenValue v x y z := by
    intro x _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  rcases ha.eq_or_lt with rfl | ha'
  ·
    rw [arm1_eq v (by omega) hX hX' (T := (((q ^ (-j))⁻¹ : ℝ) : ℂ) *
        (residueCardC v ^ N * (1 + ((-(0 : ℤ) - j : ℤ) : ℂ) * (1 - (residueCardC v)⁻¹))))
        (fun x hx hx' => inner_sum_shell_x_of_small v (by omega) hy hZ hZ' (hX x hx) hx')]
    have harm2 : ∀ x ∈ X, ballIndicatorAt v (j + 1) x *
          ∑ z ∈ Z, (1 - ballIndicatorAt v (j + 1) z) * sphericalOpenValue v x y z =
        ballIndicatorAt v (j + 1) x *
          ((((q ^ (-j))⁻¹ : ℝ) : ℂ) * (residueCardC v ^ N * (1 - (residueCardC v)⁻¹))) := by
      intro x _
      by_cases hx' : Valued.v x ≤ WithZero.exp (-(j + 1))
      · rw [inner_sum_shell_z v (by omega) hy hZ hx', W_of_small v (by omega) hy hZ hZ' hx']
      · rw [ballIndicatorAt_of_not_le v hx', zero_mul, zero_mul]
    rw [Finset.sum_congr rfl harm2, ← Finset.sum_mul, count_sub_box_eq_zpow v (by omega) (by omega) hX']
    simp only [Complex.ofReal_zpow, Complex.ofReal_natCast, residueCardC, zpow_neg, inv_inv,
      zpow_sub₀ hQ, zpow_add₀ hQ, zpow_natCast, zpow_one, zpow_zero]
    push_cast
    field_simp
    ring
  ·
    rw [arm1_eq v (by omega) hX hX' (T := (((q ^ (-j))⁻¹ : ℝ) : ℂ) * (Q ^ ((N : ℤ) - j) * (((q ^ (a - j))⁻¹ : ℝ) : ℂ)))
        (fun x hx hx' => inner_sum_shell_x_of_large v ha' hja hy hZ hZ' (hX x hx) hx')]
    have harm2 : ∀ x ∈ X, ballIndicatorAt v (j + 1) x *
          ∑ z ∈ Z, (1 - ballIndicatorAt v (j + 1) z) * sphericalOpenValue v x y z =
        (((q ^ (-j))⁻¹ : ℝ) : ℂ) *
          (residueCardC v ^ N * (1 - (residueCardC v)⁻¹) * ballIndicatorAt v (j + a + 1) x +
            residueCardC v ^ N * (1 - (residueCardC v)⁻¹) * ((1 - a - j : ℤ) : ℂ) *
              (ballIndicatorAt v (j + a) x - ballIndicatorAt v (j + a + 1) x) +
            Q ^ ((N : ℤ) - j) * (1 - Q⁻¹) * (((q ^ a)⁻¹ : ℝ) : ℂ) *
              (ballIndicatorAt v (j + 1) x * (((max (q ^ (-(j + a))) ‖x‖)⁻¹ : ℝ) : ℂ) -
                (((q ^ (a + j)) : ℝ) : ℂ) * ballIndicatorAt v (j + a) x)) := by
      intro x _
      by_cases hx' : Valued.v x ≤ WithZero.exp (-(j + 1))
      · rw [inner_sum_shell_z v (by omega) hy hZ hx', W_of_large v ha' hja hy hZ hZ' hx', ballIndicatorAt_of_le v hx',
          one_mul, one_mul]
      · have h2 : ¬ Valued.v x ≤ WithZero.exp (-(j + a)) := fun h =>
          hx' (h.trans (WithZero.exp_le_exp.2 (by omega)))
        have h1 : ¬ Valued.v x ≤ WithZero.exp (-(j + a + 1)) := fun h =>
          hx' (h.trans (WithZero.exp_le_exp.2 (by omega)))
        rw [ballIndicatorAt_of_not_le v hx', ballIndicatorAt_of_not_le v h2, ballIndicatorAt_of_not_le v h1]
        ring
    rw [Finset.sum_congr rfl harm2, ← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [count_sub_box_eq_zpow v (by omega) (by omega) hX' (i := j + a + 1),
      count_sub_box_eq_zpow v (by omega) (by omega) hX' (i := j + a),
      sum_ballIndicatorAt_mul_inv_max_zpow_norm v (a := -(j + a)) (by omega) (by omega : j ≤ j + 1) (by omega) hX hX']
    simp only [Complex.ofReal_inv, Complex.ofReal_zpow, Complex.ofReal_natCast, residueCardC, zpow_neg, inv_inv,
      zpow_sub₀ hQ, zpow_add₀ hQ, zpow_natCast, zpow_one]
    push_cast
    field_simp
    ring

end LanglandsTunnell.CubicInduction

end JoinPiece_OpenValueH4

section JoinPiece_OpenValueH5

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "q" => (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ)
local notation "Q" => ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ)
local notation "ϖ" => (uniformizerUnit ℚ v : v.adicCompletion ℚ)

private theorem valued_div_uniformizerUnit_of_eq (t : v.adicCompletion ℚ) {c : ℤ} (ht : Valued.v t = WithZero.exp c) :
    Valued.v (t / ϖ) = WithZero.exp (c + 1) := by
  rw [map_div₀, ht, AdelicLevel.valued_uniformizerUnit, WithZero.exp_add, WithZero.exp_neg, div_eq_mul_inv, inv_inv]

private theorem valued_div_sub_div_le {n : ℕ} {s t : v.adicCompletion ℚ}
    (h : Valued.v (s - t) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))) :
    Valued.v (s / ϖ - t / ϖ) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [← sub_div, map_div₀, AdelicLevel.valued_uniformizerUnit, div_le_iff₀ (by simp), ← WithZero.exp_add]
  exact h.trans (WithZero.exp_le_exp.2 (by push_cast; omega))

private theorem sphericalOpenValue_const_x (n : ℕ) (y z : v.adicCompletion ℚ) :
    ∀ s t : v.adicCompletion ℚ, Valued.v (s - t) ≤ WithZero.exp (-(n : ℤ)) →
      sphericalOpenValue v s y z = sphericalOpenValue v t y z := by
  intro s t hst
  have h0 : Valued.v (s - t) ≤ WithZero.exp (-(0 : ℤ)) := hst.trans (WithZero.exp_le_exp.2 (by omega))
  simp only [sphericalOpenValue]
  rw [sphericalOpenProfile_eq_of_integral_sub v y h0 (by simp : Valued.v (z - z) ≤ WithZero.exp (-(0 : ℤ)))]

private theorem max_eq_norm_z_of_lt {k c : ℤ} (hk : k ≤ 0) (hkc : -k < c) {x z' : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ WithZero.exp (-k)) (hz' : Valued.v z' = WithZero.exp c) :
    max (max (1 : ℝ) ‖x‖) ‖z'‖ = ‖z'‖ := by
  rw [norm_eq_zpow_of_valued_eq v hz']
  refine max_eq_right (max_le ?_ ?_)
  · simpa using zpow_le_zpow_right₀ (one_le_residueCard_real v) (show (0 : ℤ) ≤ c by omega)
  · exact (norm_le_zpow_of_valued_le v hx).trans (zpow_le_zpow_right₀ (one_le_residueCard_real v) hkc.le)

private theorem sum_value_of_far {k c : ℤ} (hk : k ≤ 0) (hkc : -k < c) {N : ℕ} (hkN : k ≤ (N : ℤ))
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {y z' : v.adicCompletion ℚ} (hz' : Valued.v z' = WithZero.exp c) (hy : ‖y‖ ≤ ‖z'‖)
    (hfar : ∀ x ∈ X, Valued.v (y * x) < Valued.v z') :
    ∑ x ∈ X, sphericalOpenValue v x y z' = Q ^ ((N : ℤ) - k) * ((((q ^ c) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hone : (1 : ℝ) ≤ ‖z'‖ := by
    rw [norm_eq_zpow_of_valued_eq v hz']
    simpa using zpow_le_zpow_right₀ (one_le_residueCard_real v) (show (0 : ℤ) ≤ c by omega)
  have hval : ∀ x ∈ X, sphericalOpenValue v x y z' = ((((q ^ c) ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro x hx
    simp only [sphericalOpenValue]
    rw [norm_sub_rev, norm_sub_eq_of_valued_lt v (hfar x hx), max_eq_norm_z_of_lt v hk hkc (hX x hx) hz',
      max_eq_right (max_le hone hy), norm_eq_zpow_of_valued_eq v hz', sq]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← card_system_eq_zpow v hkN hX hX', Finset.sum_const, nsmul_eq_mul, mul_one]

private theorem inv_max_norm_mul {Y w : ℝ} (hY : 0 < Y) : (max Y (Y * w))⁻¹ = Y⁻¹ * (max (q ^ (0 : ℤ)) w)⁻¹ := by
  rw [zpow_zero]
  rcases le_total 1 w with h | h
  · rw [max_eq_right h, max_eq_right (le_mul_of_one_le_right hY.le h), mul_inv]
  · rw [max_eq_left h, max_eq_left (mul_le_of_le_one_right hY.le h), inv_one, mul_one]

private theorem sum_value_of_near {k b c : ℤ} (hk : k ≤ 0) (hkc : -k < c) (hb : 0 < b) (hcb : c - b ≤ -k) {N : ℕ}
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {y z' : v.adicCompletion ℚ} (hyv : Valued.v y = WithZero.exp b) (hz' : Valued.v z' = WithZero.exp c) :
    ∑ x ∈ X, sphericalOpenValue v x y z' =
      (((q ^ c)⁻¹ : ℝ) : ℂ) * ((((q ^ b)⁻¹ : ℝ) : ℂ) *
        (residueCardC v ^ N * (1 + ((-(0 : ℤ) - k : ℤ) : ℂ) * (1 - (residueCardC v)⁻¹)))) := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hyv
    exact absurd hyv.symm (ne_of_gt (by simp))
  have hyn : ‖y‖ = q ^ b := norm_eq_zpow_of_valued_eq v hyv
  have hypos : (0 : ℝ) < q ^ b := zpow_pos (residueCard_real_pos v) b
  have hmaxy : max (1 : ℝ) ‖y‖ = ‖y‖ := max_eq_right (by
    rw [hyn]; exact le_trans (by simp) (zpow_le_zpow_right₀ (one_le_residueCard_real v) (show (0 : ℤ) ≤ b by omega)))
  have hcz : Valued.v (z' / y) ≤ WithZero.exp (-k) := by
    rw [map_div₀, hyv, hz', div_le_iff₀ (by simp), ← WithZero.exp_add]
    exact WithZero.exp_le_exp.2 (by omega)
  have hval : ∀ x ∈ X, sphericalOpenValue v x y z' =
      (((q ^ c)⁻¹ : ℝ) : ℂ) * ((((q ^ b)⁻¹ : ℝ) : ℂ) * (((max (q ^ (0 : ℤ)) ‖x - z' / y‖)⁻¹ : ℝ) : ℂ)) := by
    intro x hx
    have hrw : z' - y * x = y * (z' / y - x) := by rw [mul_sub, mul_comm y (z' / y), div_mul_cancel₀ z' hy0]
    have hreal : (max (max (1 : ℝ) ‖y‖) ‖z' - y * x‖ * max (max (1 : ℝ) ‖x‖) ‖z'‖)⁻¹ =
        (q ^ c)⁻¹ * ((q ^ b)⁻¹ * (max (q ^ (0 : ℤ)) ‖x - z' / y‖)⁻¹) := by
      rw [max_eq_norm_z_of_lt v hk hkc (hX x hx) hz', hmaxy, hrw, norm_mul, mul_inv,
        inv_max_norm_mul v (norm_pos_iff.2 hy0), norm_eq_zpow_of_valued_eq v hz', hyn, norm_sub_rev (z' / y) x]
      ring
    simp only [sphericalOpenValue]
    rw [hreal, Complex.ofReal_mul, Complex.ofReal_mul]

  rw [Finset.sum_congr rfl hval, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_sub_eq_sum_of_representatives v hX hX' hcz (coupled_const v le_rfl N),
    sum_inv_max_zpow_norm v le_rfl (by omega) hX hX']

private theorem sum_word11_sphericalOpenValue_eq_zero_of_lt_norm {kx : ℤ} (hkx : kx ≤ 0) {N : ℕ} (hN : 2 ≤ N)
    {X : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-kx))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-kx) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {y z : v.adicCompletion ℚ} (hy : ‖y‖ ≤ (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ (-kx))
    (hz : (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ) ^ (-kx) < ‖z‖) :
    ∑ x ∈ X, (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
      residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
  have hQ : Q ≠ 0 := Q_ne_zero v

  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz
    linarith [zpow_pos (residueCard_real_pos v) (-kx)]
  have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  set c : ℤ := WithZero.log (Valued.v z) with hc_def
  have hzc : Valued.v z = WithZero.exp c := (WithZero.exp_log hvz).symm
  have hkc : -kx < c := by
    by_contra h
    push Not at h
    have := norm_le_zpow_of_valued_le v (t := z) (n := -kx) (by rw [hzc]; exact WithZero.exp_le_exp.2 h)
    linarith
  have hz1 : Valued.v (z / ϖ) = WithZero.exp (c + 1) := valued_div_uniformizerUnit_of_eq v z hzc
  have hz2 : Valued.v (z / ϖ / ϖ) = WithZero.exp (c + 1 + 1) := valued_div_uniformizerUnit_of_eq v _ hz1

  obtain ⟨X₁, hX₁, hX₁', -⟩ := exists_finset_ball_representatives v (kx - 1) ((n + 1 : ℕ) : ℤ) (by push_cast; omega)
  obtain ⟨X₂, hX₂, hX₂', -⟩ :=
    exists_finset_ball_representatives v (kx - 1 - 1) ((n + 1 : ℕ) : ℤ) (by push_cast; omega)

  have hd1 : ∑ x ∈ X, sphericalOpenValue v (x / ϖ) y (z / ϖ) = Q⁻¹ * ∑ x ∈ X₁, sphericalOpenValue v x y (z / ϖ) :=
    sum_div_uniformizerUnit_eq_inv_mul_sum v (by omega) hX hX' hX₁ hX₁' (sphericalOpenValue_const_x v n y (z / ϖ))
  have hd2 : ∑ x ∈ X, sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ) =
      Q⁻¹ * (Q⁻¹ * ∑ x ∈ X₂, sphericalOpenValue v x y (z / ϖ / ϖ)) := by
    rw [sum_div_uniformizerUnit_eq_inv_mul_sum v (by omega) hX hX' hX₁ hX₁'
        (g := fun t => sphericalOpenValue v (t / ϖ) y (z / ϖ / ϖ)) (fun s t hst => by
          obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
          exact sphericalOpenValue_const_x v m y (z / ϖ / ϖ) _ _ (valued_div_sub_div_le v hst)),
      sum_div_uniformizerUnit_eq_inv_mul_sum v (by omega) hX₁ hX₁' hX₂ hX₂'
        (sphericalOpenValue_const_x v n y (z / ϖ / ϖ))]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hd1, hd2]

  by_cases hy0 : y = 0
  · subst hy0
    have hfar : ∀ (X' : Finset (v.adicCompletion ℚ)) (z' : v.adicCompletion ℚ), z' ≠ 0 → ∀ x ∈ X',
        Valued.v ((0 : v.adicCompletion ℚ) * x) < Valued.v z' := fun _ _ hz' _ _ => by
      rw [zero_mul, map_zero]; exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz')
    have hz1' : z / ϖ ≠ 0 := by rintro h; rw [h, map_zero] at hz1; exact WithZero.exp_ne_zero hz1.symm
    have hz2' : z / ϖ / ϖ ≠ 0 := by rintro h; rw [h, map_zero] at hz2; exact WithZero.exp_ne_zero hz2.symm
    have hnorm0 : ∀ t : v.adicCompletion ℚ, ‖(0 : v.adicCompletion ℚ)‖ ≤ ‖t‖ := fun t => by
      rw [norm_zero]; exact norm_nonneg _
    rw [sum_value_of_far v hkx hkc (by push_cast; omega) hX hX' hzc (hnorm0 _) (hfar X z hz0),
      sum_value_of_far v (by omega) (by omega) (by push_cast; omega) hX₁ hX₁' hz1 (hnorm0 _) (hfar X₁ _ hz1'),
      sum_value_of_far v (by omega) (by omega) (by push_cast; omega) hX₂ hX₂' hz2 (hnorm0 _) (hfar X₂ _ hz2')]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_zpow, Complex.ofReal_natCast, residueCardC,
      zpow_sub₀ hQ, zpow_add₀ hQ, zpow_natCast, zpow_one]
    field_simp
    ring
  have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  set b : ℤ := WithZero.log (Valued.v y) with hb_def
  have hyb : Valued.v y = WithZero.exp b := (WithZero.exp_log hvy).symm
  have hyn : ‖y‖ = q ^ b := norm_eq_zpow_of_valued_eq v hyb
  have hbk : b ≤ -kx := by
    rw [hyn] at hy
    exact (zpow_le_zpow_iff_right₀ (one_lt_q v)).1 hy
  by_cases hreg : b - kx < c
  ·
    have hfar : ∀ (k' : ℤ) (X' : Finset (v.adicCompletion ℚ)), (∀ r ∈ X', Valued.v r ≤ WithZero.exp (-k')) →
        ∀ (c' : ℤ) (z' : v.adicCompletion ℚ), Valued.v z' = WithZero.exp c' → b - k' < c' →
        ∀ x ∈ X', Valued.v (y * x) < Valued.v z' := by
      intro k' X' hX'' c' z' hz' hlt x hx
      rw [map_mul, hyb, hz']
      calc WithZero.exp b * Valued.v x ≤ WithZero.exp b * WithZero.exp (-k') := mul_le_mul_right (hX'' x hx) _
        _ = WithZero.exp (b + -k') := (WithZero.exp_add _ _).symm
        _ < WithZero.exp c' := WithZero.exp_lt_exp.2 (by omega)
    have hyle : ∀ (c' : ℤ) (z' : v.adicCompletion ℚ), Valued.v z' = WithZero.exp c' → b ≤ c' → ‖y‖ ≤ ‖z'‖ := by
      intro c' z' hz' hle
      rw [hyn, norm_eq_zpow_of_valued_eq v hz']
      exact zpow_le_zpow_right₀ (one_le_residueCard_real v) hle
    rw [sum_value_of_far v hkx hkc (by push_cast; omega) hX hX' hzc (hyle c z hzc (by omega))
        (hfar kx X hX c z hzc hreg),
      sum_value_of_far v (by omega) (by omega) (by push_cast; omega) hX₁ hX₁' hz1 (hyle _ _ hz1 (by omega))
        (hfar (kx - 1) X₁ hX₁ _ _ hz1 (by omega)),
      sum_value_of_far v (by omega) (by omega) (by push_cast; omega) hX₂ hX₂' hz2 (hyle _ _ hz2 (by omega))
        (hfar (kx - 1 - 1) X₂ hX₂ _ _ hz2 (by omega))]
    simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_zpow, Complex.ofReal_natCast, residueCardC,
      zpow_sub₀ hQ, zpow_add₀ hQ, zpow_natCast, zpow_one]
    field_simp
    ring
  ·
    push Not at hreg
    have hb : 0 < b := by omega
    rw [sum_value_of_near v hkx hkc hb (by omega) hX hX' hyb hzc,
      sum_value_of_near v (by omega) (by omega) hb (by omega) hX₁ hX₁' hyb hz1,
      sum_value_of_near v (by omega) (by omega) hb (by omega) hX₂ hX₂' hyb hz2]
    simp only [Complex.ofReal_inv, Complex.ofReal_zpow, Complex.ofReal_natCast, residueCardC,
      zpow_add₀ hQ, zpow_one]
    push_cast
    field_simp
    ring

end LanglandsTunnell.CubicInduction

end JoinPiece_OpenValueH5

section JoinPiece_OpenValueH6

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "q" => (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℝ)
local notation "Q" => ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : ℂ)
local notation "ϖ" => (uniformizerUnit ℚ v : v.adicCompletion ℚ)

private theorem openCellProfile_sphericalSection3 (x y z : v.adicCompletion ℚ) :
    openCellProfile v (sphericalSection3 v) x y z = sphericalOpenValue v x y z := by
  simp only [openCellProfile, sphericalSection3_openCellPoint, sphericalOpenValue]

private theorem openCellProfile_word11 (x y z : v.adicCompletion ℚ) :
    openCellProfile v (torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v)
        (sphericalSection3 v))) x y z =
      sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
        residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ) := by
  rw [openCellProfile_torusDifference_first v (torusDifference_mem_principalSeries3 v (firstTorusElement v)
      (sphericalSection3_mem v)),
    openCellProfile_torusDifference_first v (sphericalSection3_mem v),
    openCellProfile_torusDifference_first v (sphericalSection3_mem v), openCellProfile_sphericalSection3,
    openCellProfile_sphericalSection3, openCellProfile_sphericalSection3, residueCard_eq_residueCardC]
  ring

private theorem valued_div_sub_div_le_exp {m : ℤ} {s t : v.adicCompletion ℚ} (h : Valued.v (s - t) ≤ WithZero.exp m) :
    Valued.v (s / ϖ - t / ϖ) ≤ WithZero.exp (m + 1) := by
  rw [← sub_div, map_div₀, AdelicLevel.valued_uniformizerUnit, div_le_iff₀ (by simp), ← WithZero.exp_add]
  exact h.trans (WithZero.exp_le_exp.2 (by omega))

private theorem valued_mul_sub_mul_le_exp {m : ℤ} {s t : v.adicCompletion ℚ} (h : Valued.v (s - t) ≤ WithZero.exp m) :
    Valued.v (s * ϖ - t * ϖ) ≤ WithZero.exp (m - 1) := by
  rw [← sub_mul, map_mul, AdelicLevel.valued_uniformizerUnit, show m - 1 = m + -1 by ring, WithZero.exp_add]
  exact mul_le_mul_left h _

private theorem sphericalOpenValue_const (n : ℕ) (y : v.adicCompletion ℚ) {x x' z z' : v.adicCompletion ℚ}
    (hx : Valued.v (x - x') ≤ WithZero.exp (-(n : ℤ))) (hz : Valued.v (z - z') ≤ WithZero.exp (-(n : ℤ))) :
    sphericalOpenValue v x y z = sphericalOpenValue v x' y z' := by
  simp only [sphericalOpenValue]
  rw [sphericalOpenProfile_eq_of_integral_sub v y (hx.trans (WithZero.exp_le_exp.2 (by omega)))
    (hz.trans (WithZero.exp_le_exp.2 (by omega)))]

private theorem word11_const_z {n : ℕ} (hn : 2 ≤ n) (x y : v.adicCompletion ℚ) {z z' : v.adicCompletion ℚ}
    (hz : Valued.v (z - z') ≤ WithZero.exp (-(n : ℤ))) :
    sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
        residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ) =
      sphericalOpenValue v x y z' - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z' / ϖ) +
        residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z' / ϖ / ϖ) := by
  have h0 : Valued.v (x - x) ≤ WithZero.exp (-((0 : ℕ) : ℤ)) := by simp
  have h0' : Valued.v (x / ϖ - x / ϖ) ≤ WithZero.exp (-((0 : ℕ) : ℤ)) := by simp
  have h0'' : Valued.v (x / ϖ / ϖ - x / ϖ / ϖ) ≤ WithZero.exp (-((0 : ℕ) : ℤ)) := by simp
  have hz1 := valued_div_sub_div_le_exp v hz
  have hz2 := valued_div_sub_div_le_exp v hz1
  rw [sphericalOpenValue_const v 0 y h0 (hz.trans (WithZero.exp_le_exp.2 (by simp))),
    sphericalOpenValue_const v 0 y h0' (hz1.trans (WithZero.exp_le_exp.2 (by push_cast; omega))),
    sphericalOpenValue_const v 0 y h0'' (hz2.trans (WithZero.exp_le_exp.2 (by push_cast; omega)))]

private theorem zpow_lt_norm_of_not_valued_le {k : ℤ} {z : v.adicCompletion ℚ}
    (hz : ¬ Valued.v z ≤ WithZero.exp (-k)) : q ^ (-k) < ‖z‖ := by
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (by simp)
  have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  have h1 : WithZero.exp (-k + 1) ≤ Valued.v z := by
    rw [← WithZero.exp_log hvz, WithZero.exp_le_exp] at hz ⊢
    omega
  exact lt_of_lt_of_le (zpow_lt_zpow_right₀ (one_lt_q v) (by omega)) (zpow_le_norm_of_le_valued v h1)

private theorem sum_sum_div_div_eq {k : ℤ} {n : ℕ} (hkn : k ≤ (n : ℤ)) {X Z X₁ Z₁ : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)))
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-k))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)))
    (hX₁ : ∀ r ∈ X₁, Valued.v r ≤ WithZero.exp (-(k - 1)))
    (hX₁' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-(k - 1)) →
      ∃! r, r ∈ X₁ ∧ Valued.v (t - r) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)))
    (hZ₁ : ∀ r ∈ Z₁, Valued.v r ≤ WithZero.exp (-(k - 1)))
    (hZ₁' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-(k - 1)) →
      ∃! r, r ∈ Z₁ ∧ Valued.v (t - r) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)))
    {g : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ}
    (hg : ∀ a a' b b', Valued.v (a - a') ≤ WithZero.exp (-(n : ℤ)) → Valued.v (b - b') ≤ WithZero.exp (-(n : ℤ)) →
      g a b = g a' b') :
    ∑ x ∈ X, ∑ z ∈ Z, g (x / ϖ) (z / ϖ) =
      (residueCardC v)⁻¹ * ((residueCardC v)⁻¹ * ∑ x ∈ X₁, ∑ z ∈ Z₁, g x z) := by
  have hinner : ∀ x ∈ X, ∑ z ∈ Z, g (x / ϖ) (z / ϖ) = (residueCardC v)⁻¹ * ∑ z ∈ Z₁, g (x / ϖ) z := fun x _ =>
    sum_div_uniformizerUnit_eq_inv_mul_sum v hkn hZ hZ' hZ₁ hZ₁' (g := fun w => g (x / ϖ) w)
      (fun b b' hb => hg _ _ _ _ (by simp) hb)
  have houter : ∑ x ∈ X, ∑ z ∈ Z₁, g (x / ϖ) z = (residueCardC v)⁻¹ * ∑ x ∈ X₁, ∑ z ∈ Z₁, g x z :=
    sum_div_uniformizerUnit_eq_inv_mul_sum v hkn hX hX' hX₁ hX₁' (g := fun t => ∑ z ∈ Z₁, g t z)
      (fun a a' ha => Finset.sum_congr rfl fun b _ => hg _ _ _ _ ha (by simp))
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, houter]

private theorem sum_sum_indicator_eq {k k' : ℤ} (hk'k : k' ≤ k) {N : ℕ} (hkN : k ≤ (N : ℤ))
    {X Z X₁ Z₁ : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-k))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hX₁' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k') →
      ∃! r, r ∈ X₁ ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ₁' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-k') →
      ∃! r, r ∈ Z₁ ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (y : v.adicCompletion ℚ) :
    ∑ x ∈ X₁, ∑ z ∈ Z₁, ballIndicatorAt v k x * ballIndicatorAt v k z * sphericalOpenValue v x y z =
      ∑ x ∈ X, ∑ z ∈ Z, sphericalOpenValue v x y z := by
  have hind : ∀ s t : v.adicCompletion ℚ, Valued.v (s - t) ≤ WithZero.exp (-(N : ℤ)) →
      ballIndicatorAt v k s = ballIndicatorAt v k t := indicator_const v hkN
  have hinner : ∀ x : v.adicCompletion ℚ,
      ∑ z ∈ Z₁, ballIndicatorAt v k x * ballIndicatorAt v k z * sphericalOpenValue v x y z =
        ∑ z ∈ Z, ballIndicatorAt v k x * ballIndicatorAt v k z * sphericalOpenValue v x y z := by
    intro x
    refine sum_eq_sum_of_ball_representatives_of_le v hk'k hkN ?_ ?_ hZ hZ' hZ₁'
    · intro z hz
      by_contra h
      exact hz (by rw [ballIndicatorAt_of_not_le v h, mul_zero, zero_mul])
    · intro s t hst
      rw [hind s t hst, sphericalOpenValue_const v N y (x := x) (x' := x) (by simp) hst]
  have houter : ∑ x ∈ X₁, ∑ z ∈ Z, ballIndicatorAt v k x * ballIndicatorAt v k z * sphericalOpenValue v x y z =
      ∑ x ∈ X, ∑ z ∈ Z, ballIndicatorAt v k x * ballIndicatorAt v k z * sphericalOpenValue v x y z := by
    refine sum_eq_sum_of_ball_representatives_of_le v hk'k hkN ?_ ?_ hX hX' hX₁'
    · intro x hx
      by_contra h
      exact hx (Finset.sum_eq_zero fun z _ => by rw [ballIndicatorAt_of_not_le v h, zero_mul, zero_mul])
    · intro s t hst
      exact Finset.sum_congr rfl fun z _ => by
        rw [hind s t hst, sphericalOpenValue_const v N y (z := z) (z' := z) hst (by simp)]
  rw [Finset.sum_congr rfl fun x _ => hinner x, houter]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun z hz => ?_
  rw [ballIndicatorAt_of_le v (hX x hx), ballIndicatorAt_of_le v (hZ z hz), one_mul, one_mul]

private theorem sum_sum_word11_eq {kx kz a : ℤ} (hkx : kx ≤ 0) (hzx : kz ≤ kx) (ha : 0 ≤ a) (hakx : a ≤ -kx) {N : ℕ}
    (hN : 2 ≤ N) {y : v.adicCompletion ℚ} (hy : max (1 : ℝ) ‖y‖ = q ^ a) {X Z : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-kx))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-kx) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-kz))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-kz) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ x ∈ X, ∑ z ∈ Z,
        (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
          residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) =
      residueCardC v ^ (2 * N) * (1 - (residueCardC v)⁻¹) ^ 2 / residueCardC v ^ a := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
  have hQ : Q ≠ 0 := Q_ne_zero v
  have hQa : Q ^ a ≠ 0 := zpow_ne_zero _ hQ

  obtain ⟨Z₀, hZ₀, hZ₀', -⟩ := exists_finset_ball_representatives v kx ((n + 1 : ℕ) : ℤ) (by push_cast; omega)
  obtain ⟨X₁, hX₁, hX₁', -⟩ := exists_finset_ball_representatives v (kx - 1) ((n + 1 : ℕ) : ℤ) (by push_cast; omega)
  obtain ⟨Z₁, hZ₁, hZ₁', -⟩ := exists_finset_ball_representatives v (kx - 1) ((n + 1 : ℕ) : ℤ) (by push_cast; omega)
  obtain ⟨X₂, hX₂, hX₂', -⟩ :=
    exists_finset_ball_representatives v (kx - 1 - 1) ((n + 1 : ℕ) : ℤ) (by push_cast; omega)
  obtain ⟨Z₂, hZ₂, hZ₂', -⟩ :=
    exists_finset_ball_representatives v (kx - 1 - 1) ((n + 1 : ℕ) : ℤ) (by push_cast; omega)

  have hyn : ‖y‖ ≤ q ^ (-kx) :=
    (le_max_right _ _).trans (hy.le.trans (zpow_le_zpow_right₀ (one_le_residueCard_real v) hakx))
  have hA : ∀ x ∈ X, ∑ z ∈ Z,
        (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
          residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) =
      ∑ z ∈ Z₀,
        (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
          residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) +
      ∑ z ∈ Z, (1 - ballIndicatorAt v kx z) *
        (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
          residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) := by
    intro x _
    have hres : ∑ z ∈ Z, ballIndicatorAt v kx z *
          (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
            residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) =
        ∑ z ∈ Z₀,
          (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
            residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) := by
      rw [sum_eq_sum_of_ball_representatives_of_le v hzx (by push_cast; omega)
          (fun z hz => by by_contra h; exact hz (by rw [ballIndicatorAt_of_not_le v h, zero_mul]))
          (fun s t hst => by rw [indicator_const v (by push_cast; omega) s t hst, word11_const_z v (by omega) x y hst])
          hZ₀ hZ₀' hZ']
      exact Finset.sum_congr rfl fun z hz => by rw [ballIndicatorAt_of_le v (hZ₀ z hz), one_mul]
    rw [← hres, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl hA, Finset.sum_add_distrib]
  have hextra : ∑ x ∈ X, ∑ z ∈ Z, (1 - ballIndicatorAt v kx z) *
      (sphericalOpenValue v x y z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) y (z / ϖ) +
        residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : Valued.v z ≤ WithZero.exp (-kx)
    · simp only [ballIndicatorAt_of_le v hz, sub_self, zero_mul, Finset.sum_const_zero]
    · rw [← Finset.mul_sum,
        sum_word11_sphericalOpenValue_eq_zero_of_lt_norm v hkx (by omega) hX hX' hyn
          (zpow_lt_norm_of_not_valued_le v hz),
        mul_zero]
  rw [hextra, add_zero]

  have hconst : ∀ a a' b b' : v.adicCompletion ℚ, Valued.v (a - a') ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (b - b') ≤ WithZero.exp (-(n : ℤ)) → sphericalOpenValue v a y b = sphericalOpenValue v a' y b' :=
    fun a a' b b' ha hb => sphericalOpenValue_const v n y ha hb
  have hconst' : ∀ a a' b b' : v.adicCompletion ℚ, Valued.v (a - a') ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (b - b') ≤ WithZero.exp (-(n : ℤ)) →
      sphericalOpenValue v (a / ϖ) y (b / ϖ) = sphericalOpenValue v (a' / ϖ) y (b' / ϖ) := by
    intro a a' b b' ha hb
    exact sphericalOpenValue_const v 0 y
      ((valued_div_sub_div_le_exp v ha).trans (WithZero.exp_le_exp.2 (by push_cast; omega)))
      ((valued_div_sub_div_le_exp v hb).trans (WithZero.exp_le_exp.2 (by push_cast; omega)))
  have hD1 : ∑ x ∈ X, ∑ z ∈ Z₀, sphericalOpenValue v (x / ϖ) y (z / ϖ) =
      (residueCardC v)⁻¹ * ((residueCardC v)⁻¹ * ∑ x ∈ X₁, ∑ z ∈ Z₁, sphericalOpenValue v x y z) :=
    sum_sum_div_div_eq v (by omega) hX hX' hZ₀ hZ₀' hX₁ hX₁' hZ₁ hZ₁' hconst
  have hD2 : ∑ x ∈ X, ∑ z ∈ Z₀, sphericalOpenValue v (x / ϖ / ϖ) y (z / ϖ / ϖ) =
      (residueCardC v)⁻¹ * ((residueCardC v)⁻¹ *
        ((residueCardC v)⁻¹ * ((residueCardC v)⁻¹ * ∑ x ∈ X₂, ∑ z ∈ Z₂, sphericalOpenValue v x y z))) := by
    rw [sum_sum_div_div_eq v (by omega) hX hX' hZ₀ hZ₀' hX₁ hX₁' hZ₁ hZ₁'
        (g := fun s t => sphericalOpenValue v (s / ϖ) y (t / ϖ)) hconst',
      sum_sum_div_div_eq v (by omega) hX₁ hX₁' hZ₁ hZ₁' hX₂ hX₂' hZ₂ hZ₂' hconst]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hD1, hD2]

  have hS1 : ∑ x ∈ X₁, ∑ z ∈ Z₁, sphericalOpenValue v x y z =
      ∑ x ∈ X, ∑ z ∈ Z₀, sphericalOpenValue v x y z +
        ∑ x ∈ X₁, ∑ z ∈ Z₁, (1 - ballIndicatorAt v (kx - 1 + 1) x * ballIndicatorAt v (kx - 1 + 1) z) *
          sphericalOpenValue v x y z := by
    rw [sub_add_cancel,
      ← sum_sum_indicator_eq v (by omega : kx - 1 ≤ kx) (by push_cast; omega) hX hX' hZ₀ hZ₀' hX₁' hZ₁' y,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hS2 : ∑ x ∈ X₂, ∑ z ∈ Z₂, sphericalOpenValue v x y z =
      ∑ x ∈ X₁, ∑ z ∈ Z₁, sphericalOpenValue v x y z +
        ∑ x ∈ X₂, ∑ z ∈ Z₂, (1 - ballIndicatorAt v (kx - 1 - 1 + 1) x * ballIndicatorAt v (kx - 1 - 1 + 1) z) *
          sphericalOpenValue v x y z := by
    rw [sub_add_cancel,
      ← sum_sum_indicator_eq v (by omega : kx - 1 - 1 ≤ kx - 1) (by push_cast; omega) hX₁ hX₁' hZ₁ hZ₁' hX₂' hZ₂' y,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring

  rw [hS2, hS1, sum_sum_lShell_sphericalOpenValue v ha (by omega) hy hX₁ hX₁' hZ₁ hZ₁',
    sum_sum_lShell_sphericalOpenValue v ha (by omega) hy hX₂ hX₂' hZ₂ hZ₂']
  simp only [residueCardC]
  push_cast
  field_simp
  ring

private theorem sum_sum_word_eq_indicator {kx ky kz : ℤ} (hkx : kx ≤ 0) (hxy : kx ≤ ky) (hky : ky ≤ 0)
    (hzx : kz + 1 ≤ kx) {N : ℕ} (hN : 2 ≤ N) {X Z : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-kx))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-kx) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-kz))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-kz) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ WithZero.exp (-ky)) :
    ∑ x ∈ X, ∑ z ∈ Z, openCellProfile v (torusDifference v (secondTorusElement v) (torusDifference v
        (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v)))) x y z =
      residueCardC v ^ (2 * N) * (1 - (residueCardC v)⁻¹) ^ 2 * (1 - (residueCardC v)⁻¹) * ballIndicatorAt v 0 y := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
  have hQ : Q ≠ 0 := Q_ne_zero v
  have hφ := torusDifference_mem_principalSeries3 v (firstTorusElement v)
    (torusDifference_mem_principalSeries3 v (firstTorusElement v) (sphericalSection3_mem v))

  simp only [openCellProfile_torusDifference_second v hφ, openCellProfile_word11, residueCard_eq_residueCardC,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

  obtain ⟨Z₀, hZ₀, hZ₀', -⟩ := exists_finset_ball_representatives v (kz + 1) ((n + 1 : ℕ) : ℤ) (by push_cast; omega)
  have hϖ : ϖ ≠ 0 := (uniformizerUnit ℚ v).ne_zero
  have hshrink : ∀ x : v.adicCompletion ℚ, ∑ z ∈ Z,
        (sphericalOpenValue v x (y * ϖ) (z * ϖ) -
            2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) (y * ϖ) (z * ϖ / ϖ) +
          residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) (y * ϖ) (z * ϖ / ϖ / ϖ)) =
      residueCardC v * ∑ z ∈ Z₀,
        (sphericalOpenValue v x (y * ϖ) z - 2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) (y * ϖ) (z / ϖ) +
          residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) (y * ϖ) (z / ϖ / ϖ)) := by
    intro x
    have hkz : kz + 1 - 1 = kz := by ring
    have hZm : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-(kz + 1 - 1)) := by rw [hkz]; exact hZ
    have hZm' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-(kz + 1 - 1)) →
        ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by rw [hkz]; exact hZ'
    have key := sum_div_uniformizerUnit_eq_inv_mul_sum v (by push_cast; omega) hZ₀ hZ₀' hZm hZm'
      (g := fun w => sphericalOpenValue v x (y * ϖ) (w * ϖ) -
          2 * residueCardC v ^ 2 * sphericalOpenValue v (x / ϖ) (y * ϖ) (w * ϖ / ϖ) +
        residueCardC v ^ 4 * sphericalOpenValue v (x / ϖ / ϖ) (y * ϖ) (w * ϖ / ϖ / ϖ))
      (fun s t hst => word11_const_z v (n := n + 1) (by omega) x (y * ϖ)
        ((valued_mul_sub_mul_le_exp v hst).trans (WithZero.exp_le_exp.2 (by push_cast; omega))))
    simp only [div_mul_cancel₀ _ hϖ] at key
    rw [← inv_mul_eq_iff_eq_mul₀ (show residueCardC v ≠ 0 from natCast_natCard_quot_ne_zero v)]
    exact key.symm
  simp only [hshrink, ← Finset.mul_sum]

  by_cases hy0 : Valued.v y ≤ WithZero.exp (-(0 : ℤ))
  ·
    have hy1 : max (1 : ℝ) ‖y‖ = q ^ (0 : ℤ) := by
      rw [zpow_zero]; exact max_eq_left (by simpa using norm_le_zpow_of_valued_le v hy0)
    have hvyϖ : Valued.v (y * ϖ) ≤ WithZero.exp (-(0 : ℤ)) := by
      rw [map_mul, AdelicLevel.valued_uniformizerUnit]
      calc Valued.v y * WithZero.exp (-1 : ℤ) ≤ WithZero.exp (-(0 : ℤ)) * WithZero.exp (-1 : ℤ) :=
            mul_le_mul_left hy0 _
        _ ≤ WithZero.exp (-(0 : ℤ)) := by rw [← WithZero.exp_add]; exact WithZero.exp_le_exp.2 (by omega)
    have hyϖ : max (1 : ℝ) ‖y * ϖ‖ = q ^ (0 : ℤ) := by
      rw [zpow_zero]; exact max_eq_left (by simpa using norm_le_zpow_of_valued_le v hvyϖ)
    rw [sum_sum_word11_eq v hkx (by omega) le_rfl (by omega) hN hy1 hX hX' hZ hZ',
      sum_sum_word11_eq v hkx (by omega) le_rfl (by omega) hN hyϖ hX hX' hZ₀ hZ₀', ballIndicatorAt_of_le v hy0]
    simp only [residueCardC, zpow_zero]
    push_cast
    field_simp
  ·
    have hvy : Valued.v y ≠ 0 := fun h => hy0 (by rw [h]; exact zero_le')
    set a : ℤ := WithZero.log (Valued.v y) with ha_def
    have hya : Valued.v y = WithZero.exp a := (WithZero.exp_log hvy).symm
    have ha1 : 1 ≤ a := by
      rw [hya, WithZero.exp_le_exp] at hy0; omega
    have haky : a ≤ -ky := by
      rw [hya, WithZero.exp_le_exp] at hy; exact hy
    have hmax : ∀ {t : v.adicCompletion ℚ} {e : ℤ}, 0 ≤ e → Valued.v t = WithZero.exp e → max (1 : ℝ) ‖t‖ = q ^ e := by
      intro t e he ht
      rw [norm_eq_zpow_of_valued_eq v ht]
      exact max_eq_right (by simpa using zpow_le_zpow_right₀ (one_le_residueCard_real v) he)
    have hyϖ : Valued.v (y * ϖ) = WithZero.exp (a - 1) := by
      rw [map_mul, hya, AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_add, sub_eq_add_neg]
    rw [sum_sum_word11_eq v hkx (by omega) (by omega) (by omega) hN (hmax (by omega) hya) hX hX' hZ hZ',
      sum_sum_word11_eq v hkx (by omega) (by omega) (by omega) hN (hmax (by omega) hyϖ) hX hX' hZ₀ hZ₀',
      ballIndicatorAt_of_not_le v hy0]
    have hQa : Q ^ a ≠ 0 := zpow_ne_zero _ hQ
    simp only [residueCardC, zpow_sub₀ hQ, zpow_one]
    field_simp
    ring

private theorem sum_sum_sum_openCellProfile_word_sphericalSection3 {kx ky kz : ℤ} (hkx : kx ≤ 0) (hxy : kx ≤ ky)
    (hky : ky ≤ 0) (hzx : kz + 1 ≤ kx) {N : ℕ} (hN : 2 ≤ N) {X Y Z : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-kx))
    (hX' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-kx) →
      ∃! r, r ∈ X ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hY : ∀ r ∈ Y, Valued.v r ≤ WithZero.exp (-ky))
    (hY' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-ky) →
      ∃! r, r ∈ Y ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ)))
    (hZ : ∀ r ∈ Z, Valued.v r ≤ WithZero.exp (-kz))
    (hZ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-kz) →
      ∃! r, r ∈ Z ∧ Valued.v (t - r) ≤ WithZero.exp (-(N : ℤ))) :
    ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, openCellProfile v (torusDifference v (secondTorusElement v) (torusDifference v
        (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v)))) x y z =
      (residueCardC v - 1) ^ 3 * residueCardC v ^ (3 * N - 3) := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun y hy =>
      sum_sum_word_eq_indicator v hkx hxy hky hzx hN hX hX' hZ hZ' (hY y hy),
    ← Finset.mul_sum, count_sub_box_eq_zpow v hky (by omega) hY']
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
  have hQ : Q ≠ 0 := Q_ne_zero v
  rw [show 3 * (n + 1) - 3 = 3 * n by omega]
  simp only [residueCardC, sub_zero, zpow_natCast]
  field_simp
  ring

end LanglandsTunnell.CubicInduction

end JoinPiece_OpenValueH6

section JoinPiece_WitnessGeneric

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem torusDifference_apply (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    torusDifference v a f g = f g - (halfModulus3 v a)⁻¹ * f (g * diagonal3 v a) :=
  rfl

private theorem cornerEntry_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    cornerEntry v (g * diagonal3 v a) = cornerEntry v g * (a 0 : v.adicCompletion ℚ) :=
  gl3Entry_mul_diagonal3 v g a 2 0

private theorem lowerMinor_mul_diagonal3 (g : LocalGL3 v) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (g * diagonal3 v a) = lowerMinor v g * ((a 0 : v.adicCompletion ℚ) * a 1) := by
  simp only [lowerMinor, gl3Entry_mul_diagonal3]
  ring

private theorem
    torusDifference_apply_eq_zero_of_triangular {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v fun _ => 1)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0)
    (h21 : gl3Entry v g 2 1 = 0) : torusDifference v a f g = 0 := by
  refine apply_eq_zero_of_apply_one_eq_zero v (torusDifference_mem_principalSeries3 v a hf) ?_ g h20 h10 h21
  rw [torusDifference_apply, one_mul, ← mul_one (diagonal3 v a), apply_diagonal3_mul_of_mem_principalSeries3 hf,
    torusChar3_one_apply, one_mul, inv_mul_cancel_left₀ (halfModulus3_ne_zero v a), sub_self]

private theorem torusDifference_apply_eq_zero_of_forall_lengthLeOne {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 → f g = 0)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) (h20 : cornerEntry v g = 0)
    (h : gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0) : torusDifference v a f g = 0 := by
  rw [torusDifference_apply, hf g h20 h, hf _ (by rw [cornerEntry_mul_diagonal3, h20, zero_mul])
    (by rw [gl3Entry_mul_diagonal3, gl3Entry_mul_diagonal3, mul_mul_mul_comm, h, zero_mul]), mul_zero, sub_zero]

private theorem torusDifference_apply_eq_zero_of_forall_cornerEntry {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → f g = 0) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) : torusDifference v a f g = 0 := by
  rw [torusDifference_apply, hf g h20, hf _ (by rw [cornerEntry_mul_diagonal3, h20, zero_mul]), mul_zero, sub_zero]

private theorem torusDifference_apply_eq_zero_of_forall_mul_lowerMinor {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → f g = 0) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (h : cornerEntry v g * lowerMinor v g = 0) : torusDifference v a f g = 0 := by
  rw [torusDifference_apply, hf g h, hf _ (by rw [cornerEntry_mul_diagonal3, lowerMinor_mul_diagonal3,
    mul_mul_mul_comm, h, zero_mul]), mul_zero, sub_zero]

private theorem levelAvg_apply_eq_zero_of_forall_lengthLeOne {S : Finset (LocalGL3 v)}
    (hS : ∀ s ∈ S, ∃ x y z : v.adicCompletion ℚ, s = upperUnipotent3 x y z) {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 → f g = 0)
    (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h : gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0) :
    levelAvg v S f g = 0 := by
  rw [levelAvg_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s hs => ?_)
  obtain ⟨x, y, z, rfl⟩ := hS s hs
  exact hf _ (by rw [cornerEntry_mul_upperUnipotent3, h20])
    (by rw [gl3Entry_mul_upperUnipotent3_one_zero, gl3Entry_mul_upperUnipotent3_two_one, h20, zero_mul, zero_add, h])

private theorem levelAvg_apply_eq_zero_of_forall_cornerEntry {S : Finset (LocalGL3 v)}
    (hS : ∀ s ∈ S, ∃ x y z : v.adicCompletion ℚ, s = upperUnipotent3 x y z) {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → f g = 0) (g : LocalGL3 v) (h20 : cornerEntry v g = 0) :
    levelAvg v S f g = 0 := by
  rw [levelAvg_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s hs => ?_)
  obtain ⟨x, y, z, rfl⟩ := hS s hs
  exact hf _ (by rw [cornerEntry_mul_upperUnipotent3, h20])

private theorem levelAvg_apply_eq_zero_of_forall_mul_lowerMinor {S : Finset (LocalGL3 v)}
    (hS : ∀ s ∈ S, ∃ x y z : v.adicCompletion ℚ, s = upperUnipotent3 x y z) {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → f g = 0) (g : LocalGL3 v)
    (h : cornerEntry v g * lowerMinor v g = 0) : levelAvg v S f g = 0 := by
  rw [levelAvg_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s hs => ?_)
  obtain ⟨x, y, z, rfl⟩ := hS s hs
  exact hf _ (by rw [cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, h])

private theorem apply_torusDifference_eq_zero (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hT : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))) :
    Λ ⟨torusDifference v a f, torusDifference_mem_principalSeries3 v a f.2⟩ = 0 := by
  have h : (⟨torusDifference v a f, torusDifference_mem_principalSeries3 v a f.2⟩ :
      ↥(principalSeries3 v (fun _ => 1))) =
        f - (halfModulus3 v a)⁻¹ • ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ :=
    Subtype.ext rfl
  rw [h, map_sub, map_smul, hT, torusChar3_one_apply, one_mul, smul_eq_mul,
    inv_mul_cancel_left₀ (halfModulus3_ne_zero v a), sub_self]

private theorem apply_levelAvg_eq (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    {S : Finset (LocalGL3 v)} (hS0 : S.Nonempty)
    (hS : ∀ s ∈ S, ∃ x y z : v.adicCompletion ℚ, s = upperUnipotent3 x y z)
    (f : ↥(principalSeries3 v (fun _ => 1))) :
    Λ ⟨levelAvg v S f, levelAvg_mem_principalSeries3 v S f.2⟩ = Λ f := by
  have h : (⟨levelAvg v S f, levelAvg_mem_principalSeries3 v S f.2⟩ : ↥(principalSeries3 v (fun _ => 1))) =
      (S.card : ℂ)⁻¹ • ∑ s ∈ S, (⟨gl3AmbientRightTranslate (R := ℂ) s f, rightTranslate_mem_principalSeries3 f.2 s⟩ :
        ↥(principalSeries3 v (fun _ => 1))) := by
    ext g
    simp [levelAvg_apply, Finset.sum_apply]
  have hterm : ∀ s ∈ S, Λ (⟨gl3AmbientRightTranslate (R := ℂ) s f, rightTranslate_mem_principalSeries3 f.2 s⟩ :
      ↥(principalSeries3 v (fun _ => 1))) = Λ f := by
    intro s hs
    obtain ⟨x, y, z, rfl⟩ := hS s hs
    exact hN x y z f
  have hcard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast hS0.card_pos.ne'
  rw [h, map_smul, map_sum, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, smul_eq_mul,
    inv_mul_cancel_left₀ hcard]

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_WitnessGeneric

section JoinPiece_WitnessGeneric2

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem torusDifference_apply_eq_zero_of_forall_firstClosure {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → f g = 0) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h21 : gl3Entry v g 2 1 = 0) : torusDifference v a f g = 0 := by
  rw [torusDifference_apply, hf g h20 h21, hf _ (by rw [cornerEntry_mul_diagonal3, h20, zero_mul])
    (by rw [gl3Entry_mul_diagonal3, h21, zero_mul]), mul_zero, sub_zero]

private theorem torusDifference_apply_eq_zero_of_forall_secondClosure {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → f g = 0) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0) : torusDifference v a f g = 0 := by
  rw [torusDifference_apply, hf g h20 h10, hf _ (by rw [cornerEntry_mul_diagonal3, h20, zero_mul])
    (by rw [gl3Entry_mul_diagonal3, h10, zero_mul]), mul_zero, sub_zero]

private theorem levelAvg_apply_eq_zero_of_forall_secondClosure {S : Finset (LocalGL3 v)}
    (hS : ∀ s ∈ S, ∃ x y z : v.adicCompletion ℚ, s = upperUnipotent3 x y z) {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → f g = 0) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0) : levelAvg v S f g = 0 := by
  rw [levelAvg_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s hs => ?_)
  obtain ⟨x, y, z, rfl⟩ := hS s hs
  exact hf _ (by rw [cornerEntry_mul_upperUnipotent3, h20]) (by rw [gl3Entry_mul_upperUnipotent3_one_zero, h10])

private theorem levelAvg_apply_eq_zero_of_forall_firstClosure {S : Finset (LocalGL3 v)}
    (hS : ∀ s ∈ S, ∃ x y z : v.adicCompletion ℚ, s = upperUnipotent3 x y z) {f : LocalGL3 v → ℂ}
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 → f g = 0) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h21 : gl3Entry v g 2 1 = 0) : levelAvg v S f g = 0 := by
  rw [levelAvg_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun s hs => ?_)
  obtain ⟨x, y, z, rfl⟩ := hS s hs
  exact hf _ (by rw [cornerEntry_mul_upperUnipotent3, h20])
    (by rw [gl3Entry_mul_upperUnipotent3_two_one, h20, zero_mul, zero_add, h21])

private theorem mem_setOf_lengthLeOne_mul {g : LocalGL3 v}
    (hg : g ∈ {g : LocalGL3 v | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0})
    (x y z : v.adicCompletion ℚ) :
    g * upperUnipotent3 x y z ∈ {g : LocalGL3 v | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0} := by
  obtain ⟨h20, h⟩ := hg
  refine ⟨by rw [cornerEntry_mul_upperUnipotent3, h20], ?_⟩
  rw [gl3Entry_mul_upperUnipotent3_one_zero, gl3Entry_mul_upperUnipotent3_two_one, h20, zero_mul, zero_add, h]

private theorem mem_setOf_cornerEntry_mul {g : LocalGL3 v} (hg : g ∈ {g : LocalGL3 v | cornerEntry v g = 0})
    (x y z : v.adicCompletion ℚ) : g * upperUnipotent3 x y z ∈ {g : LocalGL3 v | cornerEntry v g = 0} := by
  show cornerEntry v (g * upperUnipotent3 x y z) = 0
  rw [cornerEntry_mul_upperUnipotent3]
  exact hg

private theorem mem_setOf_mul_lowerMinor_mul {g : LocalGL3 v}
    (hg : g ∈ {g : LocalGL3 v | cornerEntry v g * lowerMinor v g = 0}) (x y z : v.adicCompletion ℚ) :
    g * upperUnipotent3 x y z ∈ {g : LocalGL3 v | cornerEntry v g * lowerMinor v g = 0} := by
  show cornerEntry v (g * upperUnipotent3 x y z) * lowerMinor v (g * upperUnipotent3 x y z) = 0
  rw [cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3]
  exact hg

private theorem
    upperUnipotent3_congruent {n : ℕ} {x y z : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-(n : ℤ)))
    (hy : Valued.v y ≤ WithZero.exp (-(n : ℤ))) (hz : Valued.v z ≤ WithZero.exp (-(n : ℤ))) (i j : Fin 3) :
    Valued.v (gl3Entry v (upperUnipotent3 x y z) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      ≤ WithZero.exp (-(n : ℤ)) := by
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, upperUnipotent3_coe] <;> first | exact hx | exact hy | exact hz

private theorem apply_mul_eq_of_mem_levelSubgroup {f : LocalGL3 v → ℂ} {n : ℕ}
    (hn : ∀ k : LocalGL3 v, (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ)))
      → gl3AmbientRightTranslate (R := ℂ) k f = f)
    {Bx By Bz : AddSubgroup (v.adicCompletion ℚ)} (hBx : Bx ≤ valuationBall v n) (hBy : By ≤ valuationBall v n)
    (hBz : Bz ≤ valuationBall v n) {h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz} :
    ∀ κ ∈ upperUnipotentSubgroup v Bx By Bz h, ∀ g : LocalGL3 v, f (g * κ) = f g := by
  intro κ hκ g
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hκ
  exact apply_mul_eq_of_level hn (upperUnipotent3_congruent (mem_valuationBall_iff.1 (hBx hx))
    (mem_valuationBall_iff.1 (hBy hy)) (mem_valuationBall_iff.1 (hBz hz))) g

private theorem exp_le_of_not_mem_valuationBall {n M : ℕ} (hnM : n ≤ M) {x : v.adicCompletion ℚ}
    (hx : x ∉ valuationBall v (-(M : ℤ))) : WithZero.exp (n : ℤ) ≤ Valued.v x := by
  rw [mem_valuationBall_iff, neg_neg, not_le] at hx
  exact le_trans (WithZero.exp_le_exp.2 (by exact_mod_cast hnM)) hx.le

private theorem exp_le_of_not_mem_valuationBall_two {n M : ℕ} (hnM : n ≤ M) {x : v.adicCompletion ℚ}
    (hx : x ∉ valuationBall v (-(2 * (M : ℤ)))) : WithZero.exp (n : ℤ) ≤ Valued.v x := by
  rw [mem_valuationBall_iff, neg_neg, not_le] at hx
  exact le_trans (WithZero.exp_le_exp.2 (by omega)) hx.le

private theorem exp_mul_max_le_of_not_mem_valuationBall {n M : ℕ} (hnM : n ≤ M) {y z : v.adicCompletion ℚ}
    (hy : y ∈ valuationBall v (-(M : ℤ))) (hz : z ∉ valuationBall v (-(2 * (M : ℤ)))) :
    WithZero.exp (n : ℤ) * max 1 (Valued.v y) ≤ Valued.v z := by
  rw [mem_valuationBall_iff, neg_neg] at hy
  rw [mem_valuationBall_iff, neg_neg, not_le] at hz
  have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (M : ℤ) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by exact_mod_cast Nat.zero_le M)
  calc WithZero.exp (n : ℤ) * max 1 (Valued.v y) ≤ WithZero.exp (M : ℤ) * WithZero.exp (M : ℤ) :=
        mul_le_mul' (WithZero.exp_le_exp.2 (by exact_mod_cast hnM)) (max_le h1 hy)
    _ = WithZero.exp (2 * (M : ℤ)) := by rw [← WithZero.exp_add, two_mul]
    _ ≤ Valued.v z := hz.le

private theorem apply_threeCycle_mul_eq_zero_of_not_mem {f : LocalGL3 v → ℂ} {n : ℕ}
    (hsupp : ∀ y z : v.adicCompletion ℚ,
      (WithZero.exp (n : ℤ) ≤ Valued.v y ∨ WithZero.exp (n : ℤ) * max 1 (Valued.v y) ≤ Valued.v z) →
        cornerCellProfile v f y z = 0)
    {M : ℕ} (hnM : n ≤ M) {hU : ∀ x ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)), ∀ y ∈ (⊤ : AddSubgroup _), x * y ∈ ⊤}
    {hK : ∀ x ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)), ∀ y ∈ valuationBall v (-(M : ℤ)),
      x * y ∈ valuationBall v (-(2 * (M : ℤ)))} :
    ∀ u ∈ upperUnipotentSubgroup v ⊥ ⊤ ⊤ hU,
      u ∉ upperUnipotentSubgroup v ⊥ (valuationBall v (-(M : ℤ))) (valuationBall v (-(2 * (M : ℤ)))) hK →
        f (threeCycle v * u) = 0 := by
  intro u hu hu'
  obtain ⟨x, y, z, hx, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
  obtain rfl : x = 0 := AddSubgroup.mem_bot.1 hx
  by_cases hy : y ∈ valuationBall v (-(M : ℤ))
  · have hz : z ∉ valuationBall v (-(2 * (M : ℤ))) := fun hz =>
      hu' (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨AddSubgroup.zero_mem _, hy, hz⟩)
    exact hsupp y z (Or.inr (exp_mul_max_le_of_not_mem_valuationBall hnM hy hz))
  · exact hsupp y z (Or.inl (exp_le_of_not_mem_valuationBall hnM hy))

private theorem apply_threeCycleInv_mul_eq_zero_of_not_mem {f : LocalGL3 v → ℂ} {n : ℕ}
    (hsupp : ∀ u w : v.adicCompletion ℚ,
      (WithZero.exp (n : ℤ) ≤ Valued.v u ∨ WithZero.exp (n : ℤ) ≤ Valued.v w) → minorCellProfile v f u w = 0)
    {M : ℕ} (hnM : n ≤ M) {hU : ∀ x ∈ (⊤ : AddSubgroup (v.adicCompletion ℚ)), ∀ y ∈ (⊥ : AddSubgroup _), x * y ∈ ⊤}
    {hK : ∀ x ∈ valuationBall v (-(M : ℤ)), ∀ y ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)),
      x * y ∈ valuationBall v (-(M : ℤ))} :
    ∀ u ∈ upperUnipotentSubgroup v ⊤ ⊥ ⊤ hU,
      u ∉ upperUnipotentSubgroup v (valuationBall v (-(M : ℤ))) ⊥ (valuationBall v (-(M : ℤ))) hK →
        f (threeCycleInv v * u) = 0 := by
  intro g hg hg'
  obtain ⟨x, y, z, -, hy, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hg
  obtain rfl : y = 0 := AddSubgroup.mem_bot.1 hy
  by_cases hx : x ∈ valuationBall v (-(M : ℤ))
  · have hz : z ∉ valuationBall v (-(M : ℤ)) := fun hz =>
      hg' (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hx, AddSubgroup.zero_mem _, hz⟩)
    exact hsupp x z (Or.inr (exp_le_of_not_mem_valuationBall hnM hz))
  · exact hsupp x z (Or.inl (exp_le_of_not_mem_valuationBall hnM hx))

private theorem apply_antidiagonal3_mul_eq_zero_of_not_mem {f : LocalGL3 v → ℂ} {n : ℕ}
    (hsupp : ∀ x y z : v.adicCompletion ℚ,
      (WithZero.exp (n : ℤ) ≤ Valued.v x ∨ WithZero.exp (n : ℤ) ≤ Valued.v y ∨ WithZero.exp (n : ℤ) ≤ Valued.v z) →
        openCellProfile v f x y z = 0)
    {M : ℕ} (hnM : n ≤ M) {hU : ∀ x ∈ (⊤ : AddSubgroup (v.adicCompletion ℚ)), ∀ y ∈ (⊤ : AddSubgroup _), x * y ∈ ⊤}
    {hK : ∀ x ∈ valuationBall v (-(M : ℤ)), ∀ y ∈ valuationBall v (-(M : ℤ)),
      x * y ∈ valuationBall v (-(2 * (M : ℤ)))} :
    ∀ u ∈ upperUnipotentSubgroup v ⊤ ⊤ ⊤ hU,
      u ∉ upperUnipotentSubgroup v (valuationBall v (-(M : ℤ))) (valuationBall v (-(M : ℤ)))
          (valuationBall v (-(2 * (M : ℤ)))) hK →
        f (antidiagonal3 v * u) = 0 := by
  intro g hg hg'
  obtain ⟨x, y, z, -, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hg
  by_cases hx : x ∈ valuationBall v (-(M : ℤ))
  · by_cases hy : y ∈ valuationBall v (-(M : ℤ))
    · have hz : z ∉ valuationBall v (-(2 * (M : ℤ))) := fun hz =>
        hg' (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hx, hy, hz⟩)
      exact hsupp x y z (Or.inr (Or.inr (exp_le_of_not_mem_valuationBall_two hnM hz)))
    · exact hsupp x y z (Or.inr (Or.inl (exp_le_of_not_mem_valuationBall hnM hy)))
  · exact hsupp x y z (Or.inl (exp_le_of_not_mem_valuationBall hnM hx))

private theorem forall_mem_valuationBall_mul_mem (M : ℕ) :
    ∀ x ∈ valuationBall v (-(M : ℤ)), ∀ y ∈ valuationBall v (-(M : ℤ)), x * y ∈ valuationBall v (-(2 * (M : ℤ))) :=
  fun _ hx _ hy => mul_mem_valuationBall (by ring_nf; exact le_rfl) hx hy

private theorem residueCard_ne_zero : residueCard v ≠ 0 := by
  simp only [residueCard, ne_eq, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

private theorem residueCard_ne_one : residueCard v ≠ 1 := by
  simp only [residueCard, ne_eq, Nat.cast_eq_one, Ideal.absNorm_eq_one_iff]
  exact v.isPrime.ne_top

private theorem residueCard_sub_one_ne_zero : residueCard v - 1 ≠ 0 :=
  sub_ne_zero.2 (residueCard_ne_one (v := v))

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_WitnessGeneric2

section JoinPiece_WitnessLinks

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def cornerWord : LocalGL3 v → ℂ :=
  torusDifference v (firstTorusElement v) (torusDifference v (secondTorusElement v) (sphericalSection3 v))

variable {v}

private def FirstElementKillsSecondClosure : Prop :=
  ∀ {h : LocalGL3 v → ℂ}, h ∈ principalSeries3 v (fun _ => 1) → ∀ g : LocalGL3 v, cornerEntry v g = 0 →
    gl3Entry v g 1 0 = 0 → torusDifference v (firstTorusElement v) h g = 0

private def SecondElementKillsFirstClosure : Prop :=
  ∀ {h : LocalGL3 v → ℂ}, h ∈ principalSeries3 v (fun _ => 1) → ∀ g : LocalGL3 v, cornerEntry v g = 0 →
    gl3Entry v g 2 1 = 0 → torusDifference v (secondTorusElement v) h g = 0

private theorem cornerWord_mem (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1) :
    cornerWord v ∈ principalSeries3 v fun _ => 1 :=
  torusDifference_mem_principalSeries3 v _ (torusDifference_mem_principalSeries3 v _ hφ)

private theorem cornerWord_apply_eq_zero (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1)
    (h₁ : FirstElementKillsSecondClosure (v := v)) (h₂ : SecondElementKillsFirstClosure (v := v)) (g : LocalGL3 v)
    (h20 : cornerEntry v g = 0) (h : gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0) : cornerWord v g = 0 := by
  rcases mul_eq_zero.1 h with h10 | h21
  · exact h₁ (torusDifference_mem_principalSeries3 v _ hφ) g h20 h10
  · exact torusDifference_apply_eq_zero_of_forall_firstClosure (fun g' h20' h21' => h₂ hφ g' h20' h21') _ g h20 h21

private theorem forall_mem_setOf_of_forall {f : LocalGL3 v → ℂ} {p : LocalGL3 v → Prop} (hf : ∀ g, p g → f g = 0) :
    ∀ g ∈ {g : LocalGL3 v | p g}, f g = 0 :=
  fun g hg => hf g hg

private theorem exists_cornerTransversal {M N : ℕ} (hMN : -(M : ℤ) ≤ N) :
    ∃ (Y Z : Finset (v.adicCompletion ℚ)) (S : Finset (LocalGL3 v)),
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (- -(M : ℤ)) →
        ∃! r, r ∈ Y ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (- -(2 * (M : ℤ))) →
        ∃! r, r ∈ Z ∧ Valued.v (x - r) ≤ WithZero.exp (-(N : ℤ))) ∧
      (∀ g, g ∈ S ↔ ∃ x ∈ ({0} : Finset (v.adicCompletion ℚ)), ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z) ∧
      IsTransversal
        (upperUnipotentSubgroup v ⊥ (valuationBall v (-(M : ℤ))) (valuationBall v (-(2 * (M : ℤ))))
          (forall_mem_bot_mul_mem _ _))
        (upperUnipotentSubgroup v ⊥ (valuationBall v N) (valuationBall v N) (forall_mem_bot_mul_mem _ _)) S := by
  classical
  obtain ⟨Y, hY, hY', -⟩ := exists_finset_ball_representatives (v := v) (-(M : ℤ)) N hMN
  obtain ⟨Z, hZ, hZ', -⟩ := exists_finset_ball_representatives (v := v) (-(2 * (M : ℤ))) N (by omega)
  have hS : ∀ g : LocalGL3 v, g ∈ (({0} : Finset (v.adicCompletion ℚ)) ×ˢ Y ×ˢ Z).image
      (fun p => (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v)) ↔
        ∃ x ∈ ({0} : Finset (v.adicCompletion ℚ)), ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z := by
    intro g
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, y, z, ⟨hx, hy, hz⟩, rfl⟩
      exact ⟨x, hx, y, hy, z, hz, rfl⟩
    · rintro ⟨x, hx, y, hy, z, hz, rfl⟩
      exact ⟨x, y, z, ⟨hx, hy, hz⟩, rfl⟩
  refine ⟨Y, Z, _, hY', hZ', hS, ?_⟩
  exact isTransversal_upperUnipotentSubgroup (v := v) _ _ (valuationBall_le_of_le v (by omega))
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v))
    (fun r hr => hY r hr) (fun y hy => hY' y hy) (fun r hr => hZ r hr) (fun z hz => hZ' z hz) hS

private theorem cellSum_eq_sum_sum_cornerCellProfile {Y Z : Finset (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ ({0} : Finset (v.adicCompletion ℚ)), ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z)
    (f : LocalGL3 v → ℂ) : cellSum v (threeCycle v) S f = ∑ y ∈ Y, ∑ z ∈ Z, cornerCellProfile v f y z := by
  simp only [cellSum, cornerCellProfile, cornerCellPoint]
  rw [sum_eq_sum_upperUnipotent3 (v := v) hS (fun s => f (threeCycle v * s)), Finset.sum_singleton]

private theorem apply_eq_zero_of_forall_lengthLeOne (hφ : sphericalSection3 v ∈ principalSeries3 v fun _ => 1)
    (h₁ : FirstElementKillsSecondClosure (v := v)) (h₂ : SecondElementKillsFirstClosure (v := v))
    (hfac : UpperTriangularFactors (v := v)) (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    (hT : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f)
    (h₄ : ∀ f : ↥(principalSeries3 v (fun _ => 1)),
      (∀ g : LocalGL3 v, cornerEntry v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0)
    (f : ↥(principalSeries3 v (fun _ => 1)))
    (hf : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 →
      (f : LocalGL3 v → ℂ) g = 0) :
    Λ f = 0 := by
  have hψmem : cornerWord v ∈ principalSeries3 v fun _ => 1 := cornerWord_mem hφ
  have hψZ := cornerWord_apply_eq_zero hφ h₁ h₂

  obtain ⟨nf, hnf⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ f.2
  obtain ⟨nψ, hnψ⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ hψmem
  obtain ⟨mf, hmf⟩ := cornerCellProfile_eq_zero_of_large f.2 hf
  obtain ⟨mψ, hmψ⟩ := cornerCellProfile_eq_zero_of_large hψmem hψZ
  set N : ℕ := max (max nf nψ) 1 with hNdef
  set M : ℕ := max mf mψ with hMdef
  obtain ⟨Y, Z, S, hY', hZ', hS, hStr⟩ := exists_cornerTransversal (v := v) (M := M) (N := N) (by omega)

  have hq : residueCardC v ≠ 0 := natCast_natCard_quot_ne_zero (v := v)
  have hq1 : residueCardC v ≠ 1 := by
    have := one_lt_natCard_quot (v := v)
    simp only [residueCardC, ne_eq, Nat.cast_eq_one]
    omega

  refine apply_eq_zero_of_cellSum_ne_zero (v := v) Λ
    (U := upperUnipotentSubgroup v ⊥ ⊤ ⊤ (forall_mem_bot_mul_mem _ _))
    (K := upperUnipotentSubgroup v ⊥ (valuationBall v (-(M : ℤ))) (valuationBall v (-(2 * (M : ℤ))))
      (forall_mem_bot_mul_mem _ _))
    (L := upperUnipotentSubgroup v ⊥ (valuationBall v N) (valuationBall v N) (forall_mem_bot_mul_mem _ _))
    ?_ ?_ (Z := {g : LocalGL3 v | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0})
    (Z' := {g : LocalGL3 v | cornerEntry v g = 0}) ?_ (threeCycle v) ?_ hStr ?_ ⟨cornerWord v, hψmem⟩
    (fun g hg => hψZ g hg.1 hg.2) ?_ ?_ ?_ ?_ f (fun g hg => hf g hg.1 hg.2) ?_ ?_
  ·
    intro u hu
    obtain ⟨x, y, z, hx, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
    exact upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hx, AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩
  ·
    refine forall_mem_apply_rightTranslate_eq_of_forall_upperUnipotent3 (v := v) Λ hN (fun u hu => ?_)
    obtain ⟨x, y, z, -, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
    exact ⟨x, y, z, rfl⟩
  ·
    intro g hg u hu
    obtain ⟨x, y, z, -, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
    exact mem_setOf_lengthLeOne_mul hg x y z
  ·
    intro h hh hZ hcell g hg
    refine apply_eq_zero_of_cornerEntry_eq_zero hfac hh (fun g' h20 h' => hZ g' ⟨h20, h'⟩) (fun y z => ?_) hg
    exact hcell (upperUnipotent3 0 y z) (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
      ⟨AddSubgroup.mem_bot.2 rfl, AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩)
  ·
    exact fun h hh => h₄ h (fun g hg => hh g hg)
  ·
    exact apply_mul_eq_of_mem_levelSubgroup hnψ bot_le (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))
  ·
    exact apply_threeCycle_mul_eq_zero_of_not_mem hmψ (le_max_right mf mψ)
  ·
    exact apply_torusDifference_eq_zero Λ hT (firstTorusElement v)
      ⟨_, torusDifference_mem_principalSeries3 v (secondTorusElement v) hφ⟩
  ·
    rw [cellSum_eq_sum_sum_cornerCellProfile hS]
    show (∑ y ∈ Y, ∑ z ∈ Z, cornerCellProfile v (torusDifference v (firstTorusElement v)
      (torusDifference v (secondTorusElement v) (sphericalSection3 v))) y z) ≠ 0
    rw [sum_sum_corner_word (v := v) (ky := -(M : ℤ)) (kz := -(2 * (M : ℤ))) (by omega) (by omega)
      (N := N) (by omega) hY' hZ' hq (fun y _ z _ => cornerCellProfile_word (v := v) hφ y z)]
    simp [hq, hq1, sub_eq_zero]
  ·
    exact apply_mul_eq_of_mem_levelSubgroup hnf bot_le (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))
  ·
    exact apply_threeCycle_mul_eq_zero_of_not_mem hmf (le_max_left mf mψ)

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_WitnessLinks

section JoinPiece_WitnessLinks2

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem firstElementKillsSecondClosure : FirstElementKillsSecondClosure (v := v) := by
  intro h hh g h20 h10
  rw [torusDifference_apply]
  exact sub_inv_halfModulus3_mul_apply_mul_diagonal3_left v hh (uniformizerUnit ℚ v) g h20 h10

private theorem secondElementKillsFirstClosure : SecondElementKillsFirstClosure (v := v) := by
  intro h hh g h20 h21
  rw [torusDifference_apply]
  exact sub_inv_halfModulus3_mul_apply_mul_diagonal3_right v hh (uniformizerUnit ℚ v) g h20 h21

private theorem upperTriangularFactors : UpperTriangularFactors (v := v) :=
  fun b h20 h10 h21 => exists_eq_upperUnipotent3_mul_diagonal3 v b h20 h10 h21

private theorem link3 (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    (hT : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f) :
    (∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 →
          (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0 :=
  fun h₄ f hf => apply_eq_zero_of_forall_lengthLeOne (sphericalSection3_mem v) firstElementKillsSecondClosure
    secondElementKillsFirstClosure upperTriangularFactors Λ hN hT h₄ f hf

private theorem exists_transversal_of_systems {Bx By Bz Bx' By' Bz' : AddSubgroup (v.adicCompletion ℚ)}
    (h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz) (h' : ∀ x ∈ Bx', ∀ y ∈ By', x * y ∈ Bz') (hy : By' ≤ By)
    {X Y Z : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, r ∈ Bx) (hX' : ∀ x ∈ Bx, ∃! r, r ∈ X ∧ x - r ∈ Bx')
    (hY : ∀ r ∈ Y, r ∈ By) (hY' : ∀ y ∈ By, ∃! r, r ∈ Y ∧ y - r ∈ By') (hZ : ∀ r ∈ Z, r ∈ Bz)
    (hZ' : ∀ z ∈ Bz, ∃! r, r ∈ Z ∧ z - r ∈ Bz') :
    ∃ S : Finset (LocalGL3 v), (∀ g, g ∈ S ↔ ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z) ∧
      IsTransversal (upperUnipotentSubgroup v Bx By Bz h) (upperUnipotentSubgroup v Bx' By' Bz' h') S := by
  classical
  have hS : ∀ g : LocalGL3 v, g ∈ (X ×ˢ Y ×ˢ Z).image (fun p => (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v)) ↔
      ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z := by
    intro g
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, y, z, ⟨hx, hy, hz⟩, rfl⟩
      exact ⟨x, hx, y, hy, z, hz, rfl⟩
    · rintro ⟨x, hx, y, hy, z, hz, rfl⟩
      exact ⟨x, y, z, ⟨hx, hy, hz⟩, rfl⟩
  exact ⟨_, hS, isTransversal_upperUnipotentSubgroup (v := v) h h' hy hX hX' hY hY' hZ hZ' hS⟩

private theorem forall_exists_eq_upperUnipotent3_of_forall_iff {X Y Z : Finset (v.adicCompletion ℚ)}
    {S : Finset (LocalGL3 v)} (hS : ∀ g, g ∈ S ↔ ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z) :
    ∀ s ∈ S, ∃ x y z : v.adicCompletion ℚ, s = upperUnipotent3 x y z := by
  intro s hs
  obtain ⟨x, -, y, -, z, -, rfl⟩ := (hS s).1 hs
  exact ⟨x, y, z, rfl⟩

private theorem nonempty_of_forall_iff {X Y Z : Finset (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hZ : Z.Nonempty) : S.Nonempty := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  obtain ⟨z, hz⟩ := hZ
  exact ⟨_, (hS _).2 ⟨x, hx, y, hy, z, hz, rfl⟩⟩

private theorem upperUnipotentSubgroup_le {Bx By Bz Bx' By' Bz' : AddSubgroup (v.adicCompletion ℚ)}
    {h : ∀ x ∈ Bx, ∀ y ∈ By, x * y ∈ Bz} {h' : ∀ x ∈ Bx', ∀ y ∈ By', x * y ∈ Bz'} (hx : Bx ≤ Bx') (hy : By ≤ By')
    (hz : Bz ≤ Bz') : upperUnipotentSubgroup v Bx By Bz h ≤ upperUnipotentSubgroup v Bx' By' Bz' h' := by
  intro k hk
  obtain ⟨x, y, z, hxx, hyy, hzz, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hk
  exact upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hx hxx, hy hyy, hz hzz⟩

private theorem exists_system (k m : ℤ) (hkm : k ≤ m) :
    ∃ X : Finset (v.adicCompletion ℚ), (∀ r ∈ X, r ∈ valuationBall v k) ∧
      (∀ x ∈ valuationBall v k, ∃! r, r ∈ X ∧ x - r ∈ valuationBall v m) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
        ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) ∧
      X.Nonempty := by
  obtain ⟨X, hX, hX', -⟩ := exists_finset_ball_representatives (v := v) k m hkm
  refine ⟨X, fun r hr => mem_valuationBall_iff.2 (hX r hr), fun x hx => ?_, hX', ?_⟩
  · obtain ⟨r, ⟨hr, hxr⟩, huniq⟩ := hX' x (mem_valuationBall_iff.1 hx)
    exact ⟨r, ⟨hr, mem_valuationBall_iff.2 hxr⟩, fun r' hr' => huniq r' ⟨hr'.1, mem_valuationBall_iff.1 hr'.2⟩⟩
  · obtain ⟨r, ⟨hr, -⟩, -⟩ := hX' 0 (by simp)
    exact ⟨r, hr⟩

private theorem singleton_zero_nonempty : ({0} : Finset (v.adicCompletion ℚ)).Nonempty :=
  ⟨0, Finset.mem_singleton_self 0⟩

private theorem cellSum_eq_sum_sum_minorCellProfile {U W : Finset (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ U, ∃ y ∈ ({0} : Finset (v.adicCompletion ℚ)), ∃ z ∈ W, g = upperUnipotent3 x y z)
    (f : LocalGL3 v → ℂ) : cellSum v (threeCycleInv v) S f = ∑ w ∈ W, ∑ u ∈ U, minorCellProfile v f u w := by
  simp only [cellSum, minorCellProfile, minorCellPoint]
  rw [sum_eq_sum_upperUnipotent3 (v := v) hS (fun s => f (threeCycleInv v * s))]
  simp only [Finset.sum_singleton]
  exact Finset.sum_comm

private theorem apply_threeCycleInv_mul_eq_zero_of_not_mem_box {f : LocalGL3 v → ℂ} {n : ℕ}
    (hsupp : ∀ u w : v.adicCompletion ℚ,
      (WithZero.exp (n : ℤ) ≤ Valued.v u ∨ WithZero.exp (n : ℤ) ≤ Valued.v w) → minorCellProfile v f u w = 0)
    {M : ℕ} (hnM : n ≤ M) {hU : ∀ x ∈ (⊤ : AddSubgroup (v.adicCompletion ℚ)), ∀ y ∈ (⊥ : AddSubgroup _), x * y ∈ ⊤}
    {hK : ∀ x ∈ valuationBall v (-(M : ℤ)), ∀ y ∈ (⊥ : AddSubgroup (v.adicCompletion ℚ)),
      x * y ∈ valuationBall v (-(2 * (M : ℤ)))} :
    ∀ u ∈ upperUnipotentSubgroup v ⊤ ⊥ ⊤ hU,
      u ∉ upperUnipotentSubgroup v (valuationBall v (-(M : ℤ))) ⊥ (valuationBall v (-(2 * (M : ℤ)))) hK →
        f (threeCycleInv v * u) = 0 := by
  intro g hg hg'
  obtain ⟨x, y, z, -, hy, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hg
  obtain rfl : y = 0 := AddSubgroup.mem_bot.1 hy
  by_cases hx : x ∈ valuationBall v (-(M : ℤ))
  · have hz : z ∉ valuationBall v (-(2 * (M : ℤ))) := fun hz =>
      hg' (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hx, AddSubgroup.zero_mem _, hz⟩)
    exact hsupp x z (Or.inr (exp_le_of_not_mem_valuationBall_two hnM hz))
  · exact hsupp x z (Or.inl (exp_le_of_not_mem_valuationBall hnM hx))

variable (v) in

private noncomputable def minorRawWord : LocalGL3 v → ℂ :=
  torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v))

private theorem torusDifference_firstTorusElement_eq (h : LocalGL3 v → ℂ) :
    torusDifference v (firstTorusElement v) h = uniformizerDifference v h := rfl

private theorem minorRawWord_mem : minorRawWord v ∈ principalSeries3 v fun _ => 1 :=
  torusDifference_mem_principalSeries3 v _ (torusDifference_mem_principalSeries3 v _ (sphericalSection3_mem v))

private theorem minorRawWord_apply_eq_zero (g : LocalGL3 v) (h20 : cornerEntry v g = 0) (h10 : gl3Entry v g 1 0 = 0) :
    minorRawWord v g = 0 :=
  firstElementKillsSecondClosure (torusDifference_mem_principalSeries3 v _ (sphericalSection3_mem v)) g h20 h10

private theorem
    ballIndicator_zero_eq (j : ℤ) (x : v.adicCompletion ℚ) : ballIndicator v 0 j x = ballIndicatorAt v j x := by
  simp only [ballIndicator, ballIndicatorAt, sub_zero]

private theorem absNorm_eq_residueCardC : (Ideal.absNorm v.asIdeal : ℂ) = residueCardC v := by
  simp only [residueCardC, natCard_quot_eq_absNorm]

private theorem minorRawWord_cellRep1 (x : v.adicCompletion ℚ) :
    minorRawWord v (cellRep1 v x) =
      (1 - residueCardC v) * (ballIndicatorAt v 1 x - residueCardC v * ballIndicatorAt v 2 x) := by
  rw [minorRawWord, torusDifference_firstTorusElement_eq, torusDifference_firstTorusElement_eq,
    uniformizerDifference_uniformizerDifference_sphericalSection3_cellRep1, absNorm_eq_residueCardC,
    ballIndicator_zero_eq, ballIndicator_zero_eq]

private theorem ballIndicatorAt_eq_zero_of_not_mem {j : ℤ} (hj : 0 ≤ j) {x : v.adicCompletion ℚ}
    (hx : x ∉ valuationBall v 0) : ballIndicatorAt v j x = 0 := by
  rw [mem_valuationBall_iff, neg_zero, not_le] at hx
  have h : ¬ Valued.v x ≤ WithZero.exp (-j) := not_le.2 (lt_of_le_of_lt (WithZero.exp_le_exp.2 (by omega)) hx)
  simp only [ballIndicatorAt, h, if_false]

private theorem minorRawWord_cellRep1_zero_mul_eq_zero {a : v.adicCompletion ℚ} (ha : a ∉ valuationBall v 0) :
    minorRawWord v (cellRep1 v 0 * upperUnipotent3 a 0 0) = 0 := by
  rw [← cellRep1_eq_cellRep1_zero_mul, minorRawWord_cellRep1,
    ballIndicatorAt_eq_zero_of_not_mem (j := 1) (by norm_num) ha,
    ballIndicatorAt_eq_zero_of_not_mem (j := 2) (by norm_num) ha, mul_zero, sub_zero, mul_zero]

private theorem sum_minorRawWord_cellRep1_zero_mul {m : ℕ} (hm : 2 ≤ m) {X : Finset (v.adicCompletion ℚ)}
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(0 : ℤ)) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-(m : ℤ))) :
    ∑ r ∈ X, minorRawWord v (cellRep1 v 0 * upperUnipotent3 r 0 0) = 0 := by
  have h1 := sum_ballIndicatorAt_of_representatives (v := v) (k := 0) (j := 1) (m := (m : ℤ)) (by omega) (by omega) hX'
  have h2 := sum_ballIndicatorAt_of_representatives (v := v) (k := 0) (j := 2) (m := (m : ℤ)) (by omega) (by omega) hX'
  have hpow : ((m : ℤ) - 1).toNat = ((m : ℤ) - 2).toNat + 1 := by omega
  simp only [← cellRep1_eq_cellRep1_zero_mul, minorRawWord_cellRep1]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, hpow, pow_succ]
  simp only [residueCardC]
  ring

private theorem exists_firstCorrection :
    ∃ T : Finset (LocalGL3 v), T.Nonempty ∧ (∀ t ∈ T, ∃ x y z : v.adicCompletion ℚ, t = upperUnipotent3 x y z) ∧
      (∀ t ∈ T, ∃ a ∈ valuationBall v 0, t = upperUnipotent3 a 0 0) ∧
      ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0 →
        levelAvg v T (minorRawWord v) g = 0 := by
  obtain ⟨n, hn⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ (minorRawWord_mem (v := v))
  obtain ⟨m, hm2, hnm⟩ : ∃ m : ℕ, 2 ≤ m ∧ n ≤ m := ⟨max n 2, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨X, hX, hXmem, hX', hXne⟩ := exists_system (v := v) 0 (m : ℤ) (by omega)
  obtain ⟨T, hT, hTtr⟩ := exists_transversal_of_systems (v := v)
    (forall_mul_mem_bot_mem (valuationBall v 0) ⊥) (forall_mul_mem_bot_mem (valuationBall v (m : ℤ)) ⊥) le_rfl
    hX hXmem (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v))
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v))
  have hTuni := forall_exists_eq_upperUnipotent3_of_forall_iff hT
  have hTshape : ∀ t ∈ T, ∃ a ∈ valuationBall v 0, t = upperUnipotent3 a 0 0 := by
    intro t ht
    obtain ⟨a, ha, y, hy, z, hz, rfl⟩ := (hT t).1 ht
    rw [Finset.mem_singleton] at hy hz
    subst hy hz
    exact ⟨a, hX a ha, rfl⟩

  have hrawL : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v (m : ℤ)) ⊥ ⊥
      (forall_mul_mem_bot_mem (valuationBall v (m : ℤ)) ⊥), ∀ g, minorRawWord v (g * κ) = minorRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn (valuationBall_le_of_le v (by omega)) bot_le bot_le
  have hsecond : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 1 0 = 0 → levelAvg v T (minorRawWord v) g = 0 :=
    levelAvg_apply_eq_zero_of_forall_secondClosure hTuni minorRawWord_apply_eq_zero

  have hrep : ∀ w : v.adicCompletion ℚ, levelAvg v T (minorRawWord v) (cellRep1 v w) = 0 := by
    intro w
    rw [cellRep1_eq_cellRep1_zero_mul]
    by_cases hw : w ∈ valuationBall v 0
    · rw [levelAvg_apply_mul_of_mem (v := v) hTtr hrawL (cellRep1 v 0)
        (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨hw, AddSubgroup.zero_mem _, AddSubgroup.zero_mem _⟩)]
      have hsum : cellSum v (cellRep1 v 0) T (minorRawWord v) = 0 := by
        simp only [cellSum]
        rw [sum_eq_sum_upperUnipotent3 (v := v) hT (fun s => minorRawWord v (cellRep1 v 0 * s))]
        simp only [Finset.sum_singleton]
        exact sum_minorRawWord_cellRep1_zero_mul hm2 hX'
      rw [hsum, mul_zero]
    · refine levelAvg_apply_mul_of_not_mem (v := v)
        (U := upperUnipotentSubgroup v ⊤ ⊥ ⊥ (forall_mul_mem_bot_mem ⊤ ⊥))
        (K := upperUnipotentSubgroup v (valuationBall v 0) ⊥ ⊥ (forall_mul_mem_bot_mem (valuationBall v 0) ⊥))
        (upperUnipotentSubgroup_le le_top le_rfl le_rfl) hTtr.1 (w := cellRep1 v 0) ?_
        (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
          ⟨AddSubgroup.mem_top _, AddSubgroup.zero_mem _, AddSubgroup.zero_mem _⟩)
        (fun h => hw (upperUnipotent3_mem_upperUnipotentSubgroup_iff.1 h).1)
      intro u hu huK
      obtain ⟨a, b, c, -, hb, hc, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
      obtain rfl : b = 0 := AddSubgroup.mem_bot.1 hb
      obtain rfl : c = 0 := AddSubgroup.mem_bot.1 hc
      exact minorRawWord_cellRep1_zero_mul_eq_zero
        (fun ha => huK (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2 ⟨ha, hb, hc⟩))

  have hfirst : ∀ g : LocalGL3 v, cornerEntry v g = 0 → gl3Entry v g 2 1 = 0 →
      levelAvg v T (minorRawWord v) g = 0 := by
    intro g h20 h21
    by_cases h10 : gl3Entry v g 1 0 = 0
    · exact hsecond g h20 h10
    · obtain ⟨x, y, z, a, w, rfl⟩ := exists_eq_mul_cellRep1 v g h20 h21 h10
      have hmem : levelAvg v T (minorRawWord v) ∈ principalSeries3 v fun _ => 1 :=
        levelAvg_mem_principalSeries3 v T minorRawWord_mem
      rw [apply_upperUnipotent3_mul_of_mem_principalSeries3 hmem, apply_diagonal3_mul_of_mem_principalSeries3 hmem,
        hrep, mul_zero]
  refine ⟨T, nonempty_of_forall_iff hT hXne singleton_zero_nonempty singleton_zero_nonempty, hTuni, hTshape, ?_⟩
  intro g h20 h
  rcases mul_eq_zero.1 h with h10 | h21
  · exact hsecond g h20 h10
  · exact hfirst g h20 h21

private theorem link4 (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    (hT : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f) :
    (∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0 := by
  intro h₅ f hf
  have hφ := sphericalSection3_mem v
  have hq : residueCardC v ≠ 0 := natCast_natCard_quot_ne_zero (v := v)
  have hq1 : residueCardC v ≠ 1 := by
    have := one_lt_natCard_quot (v := v)
    simp only [residueCardC, ne_eq, Nat.cast_eq_one]
    omega

  obtain ⟨T₁, hT₁ne, hT₁uni, hT₁shape, hw₁Z⟩ := exists_firstCorrection (v := v)
  set w₁ : LocalGL3 v → ℂ := levelAvg v T₁ (minorRawWord v) with hw₁def
  have hw₁mem : w₁ ∈ principalSeries3 v fun _ => 1 := levelAvg_mem_principalSeries3 v T₁ minorRawWord_mem
  have hrawmem : minorRawWord v ∈ principalSeries3 v fun _ => 1 := minorRawWord_mem

  obtain ⟨n₀, hn₀⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ hrawmem
  obtain ⟨n₁, hn₁⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ hw₁mem
  obtain ⟨M, hMw₁⟩ := cornerCellProfile_eq_zero_of_large hw₁mem hw₁Z
  obtain ⟨N, hN2, hn₀N, hn₁N⟩ : ∃ N : ℕ, 2 ≤ N ∧ n₀ ≤ N ∧ n₁ ≤ N :=
    ⟨max (max n₀ n₁) 2, le_max_right _ _, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _)⟩

  obtain ⟨Y, hY, hYmem, -, hYne⟩ := exists_system (v := v) (-(M : ℤ)) N (by omega)
  obtain ⟨Z, hZ, hZmem, hZ', hZne⟩ := exists_system (v := v) (-(2 * (M : ℤ))) N (by omega)
  obtain ⟨T₃, hT₃, hT₃tr⟩ := exists_transversal_of_systems (v := v)
    (forall_mem_bot_mul_mem (valuationBall v (-(M : ℤ))) (valuationBall v (-(2 * (M : ℤ)))))
    (forall_mem_bot_mul_mem (valuationBall v N) (valuationBall v N)) (valuationBall_le_of_le v (by omega))
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v))
    hY hYmem hZ hZmem
  have hT₃uni := forall_exists_eq_upperUnipotent3_of_forall_iff hT₃
  have hT₃ne := nonempty_of_forall_iff hT₃ singleton_zero_nonempty hYne hZne
  have hT₃shape : ∀ t ∈ T₃, ∃ y ∈ valuationBall v (-(M : ℤ)), ∃ z ∈ valuationBall v (-(2 * (M : ℤ))),
      t = upperUnipotent3 0 y z := by
    intro t ht
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := (hT₃ t).1 ht
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨y, hY y hy, z, hZ z hz, rfl⟩

  have hrawL₃ : ∀ κ ∈ upperUnipotentSubgroup v ⊥ (valuationBall v N) (valuationBall v N)
      (forall_mem_bot_mul_mem (valuationBall v N) (valuationBall v N)),
      ∀ g, minorRawWord v (g * κ) = minorRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ bot_le (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))
  have hw₁L₃ : ∀ κ ∈ upperUnipotentSubgroup v ⊥ (valuationBall v N) (valuationBall v N)
      (forall_mem_bot_mul_mem (valuationBall v N) (valuationBall v N)), ∀ g, w₁ (g * κ) = w₁ g :=
    apply_mul_eq_of_mem_levelSubgroup hn₁ bot_le (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))

  have hcornerRaw : cellSum v (threeCycle v) T₃ (minorRawWord v) = 0 := by
    rw [cellSum_eq_sum_sum_cornerCellProfile hT₃]
    exact sum_sum_cornerCellProfile_word11_eq_zero (v := v) hφ (ky := -(M : ℤ)) (kz := -(2 * (M : ℤ))) (by omega)
      (by omega) hN2 (fun r hr => mem_valuationBall_iff.1 (hY r hr)) hZ'
  have hcornerSum : cellSum v (threeCycle v) T₃ w₁ = 0 := by
    have h : cellSum v (threeCycle v) T₃ w₁ = cellSum v (threeCycle v) T₃ (minorRawWord v) := by
      rw [hw₁def]
      refine cellSum_levelAvg_of_forall (v := v) hT₁ne (fun t ht => ?_)
      obtain ⟨a, ha, rfl⟩ := hT₁shape t ht
      exact cellSum_corner_rightTranslate hrawmem hT₃tr hrawL₃
        (fun y hy => mul_mem_valuationBall (by omega) ha hy) (fun y hy => mul_mem_valuationBall (by omega) ha hy)
        (AddSubgroup.zero_mem _) (AddSubgroup.zero_mem _)
    rw [h, hcornerRaw]

  set ψ : LocalGL3 v → ℂ := levelAvg v T₃ w₁ with hψdef
  have hψmem : ψ ∈ principalSeries3 v fun _ => 1 := levelAvg_mem_principalSeries3 v T₃ hw₁mem
  have hψZ : ∀ g : LocalGL3 v, cornerEntry v g = 0 → ψ g = 0 := by
    intro g hg
    refine apply_eq_zero_of_cornerEntry_eq_zero upperTriangularFactors hψmem
      (fun g' h20 h' => levelAvg_apply_eq_zero_of_forall_lengthLeOne hT₃uni hw₁Z g' h20 h') (fun y z => ?_) hg
    rw [hψdef]
    by_cases hu : (upperUnipotent3 0 y z : LocalGL3 v) ∈ upperUnipotentSubgroup v ⊥ (valuationBall v (-(M : ℤ)))
        (valuationBall v (-(2 * (M : ℤ)))) (forall_mem_bot_mul_mem _ _)
    · rw [levelAvg_apply_mul_of_mem (v := v) hT₃tr hw₁L₃ (threeCycle v) hu, hcornerSum, mul_zero]
    · exact levelAvg_apply_mul_of_not_mem (v := v)
        (U := upperUnipotentSubgroup v ⊥ ⊤ ⊤ (forall_mem_bot_mul_mem ⊤ ⊤))
        (upperUnipotentSubgroup_le le_rfl le_top le_top) hT₃tr.1
        (apply_threeCycle_mul_eq_zero_of_not_mem hMw₁ le_rfl)
        (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
          ⟨AddSubgroup.mem_bot.2 rfl, AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩) hu

  have hΛψ : Λ ⟨ψ, hψmem⟩ = 0 := by
    have e₁ := apply_levelAvg_eq (v := v) Λ hN hT₃ne hT₃uni ⟨w₁, hw₁mem⟩
    have e₂ := apply_levelAvg_eq (v := v) Λ hN hT₁ne hT₁uni ⟨minorRawWord v, hrawmem⟩
    have e₃ := apply_torusDifference_eq_zero (v := v) Λ hT (firstTorusElement v)
      ⟨_, torusDifference_mem_principalSeries3 v (firstTorusElement v) hφ⟩
    exact e₁.trans (e₂.trans e₃)

  obtain ⟨mψ, hmψ⟩ := minorCellProfile_eq_zero_of_large hψmem hψZ
  obtain ⟨mf, hmf⟩ := minorCellProfile_eq_zero_of_large f.2 hf
  obtain ⟨nψ, hnψ⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ hψmem
  obtain ⟨nf, hnf⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ f.2
  obtain ⟨M₄, hMM₄, hmψM₄, hmfM₄⟩ : ∃ M₄ : ℕ, M ≤ M₄ ∧ mψ ≤ M₄ ∧ mf ≤ M₄ :=
    ⟨max (max M mψ) mf, le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
      le_max_right _ _⟩
  obtain ⟨N₄, hNN₄, hnψN₄, hnfN₄⟩ : ∃ N₄ : ℕ, N ≤ N₄ ∧ nψ ≤ N₄ ∧ nf ≤ N₄ :=
    ⟨max (max N nψ) nf, le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
      le_max_right _ _⟩

  obtain ⟨U', hU', hU'mem, -, -⟩ := exists_system (v := v) (-(M₄ : ℤ)) ((N₄ : ℤ) + M) (by omega)
  obtain ⟨U, hU, hUmem, hU'', -⟩ := exists_system (v := v) (-(M₄ : ℤ)) N₄ (by omega)
  obtain ⟨W, hW, hWmem, hW'', -⟩ := exists_system (v := v) (-(2 * (M₄ : ℤ))) N₄ (by omega)
  obtain ⟨R, hR, hRmem, -, -⟩ := exists_system (v := v) N₄ ((N₄ : ℤ) + M) (by omega)
  obtain ⟨W₀, hW₀, hW₀mem, -, -⟩ := exists_system (v := v) N₄ N₄ le_rfl
  obtain ⟨S', hS', hS'tr⟩ := exists_transversal_of_systems (v := v)
    (forall_mul_mem_bot_mem (valuationBall v (-(M₄ : ℤ))) (valuationBall v (-(2 * (M₄ : ℤ)))))
    (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M)) (valuationBall v N₄)) le_rfl hU' hU'mem
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v)) hW hWmem
  obtain ⟨S, hS, hStr⟩ := exists_transversal_of_systems (v := v)
    (forall_mul_mem_bot_mem (valuationBall v (-(M₄ : ℤ))) (valuationBall v (-(2 * (M₄ : ℤ)))))
    (forall_mul_mem_bot_mem (valuationBall v N₄) (valuationBall v N₄)) le_rfl hU hUmem
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v)) hW hWmem
  obtain ⟨Q, -, hQtr⟩ := exists_transversal_of_systems (v := v)
    (forall_mul_mem_bot_mem (valuationBall v N₄) (valuationBall v N₄))
    (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M)) (valuationBall v N₄)) le_rfl hR hRmem
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v)) hW₀ hW₀mem

  have hrawL' : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v ((N₄ : ℤ) + M)) ⊥ (valuationBall v N₄)
      (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M)) (valuationBall v N₄)),
      ∀ g, minorRawWord v (g * κ) = minorRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))
  have hrawLsq : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v N₄) ⊥ (valuationBall v N₄)
      (forall_mul_mem_bot_mem (valuationBall v N₄) (valuationBall v N₄)),
      ∀ g, minorRawWord v (g * κ) = minorRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))
  have hw₁L' : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v ((N₄ : ℤ) + M)) ⊥ (valuationBall v N₄)
      (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M)) (valuationBall v N₄)), ∀ g, w₁ (g * κ) = w₁ g :=
    apply_mul_eq_of_mem_levelSubgroup hn₁ (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))

  have hrawS : cellSum v (threeCycleInv v) S (minorRawWord v) ≠ 0 := by
    rw [cellSum_eq_sum_sum_minorCellProfile hS]
    show (∑ w ∈ W, ∑ u ∈ U, minorCellProfile v (torusDifference v (firstTorusElement v)
      (torusDifference v (firstTorusElement v) (sphericalSection3 v))) u w) ≠ 0
    rw [sum_sum_minor_word (v := v) (ku := -(M₄ : ℤ)) (kw := -(2 * (M₄ : ℤ))) (by omega) (by omega) (N := N₄)
      (by omega) hU'' hW'' (ρ := fun w => (((max 1 ‖w‖)⁻¹ : ℝ) : ℂ))
      (fun u _ w _ => minorCellProfile_word (v := v) hφ u w)]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hq1)) (pow_ne_zero _ (pow_ne_zero _ hq))
  have hrawS' : cellSum v (threeCycleInv v) S' (minorRawWord v) ≠ 0 :=
    cellSum_ne_zero_of_refine (v := v)
      (upperUnipotentSubgroup_le (valuationBall_le_of_le v (by omega)) le_rfl (valuationBall_le_of_le v (by omega)))
      (upperUnipotentSubgroup_le (valuationBall_le_of_le v (by omega)) le_rfl le_rfl) hS'tr hStr hQtr
      (threeCycleInv v) hrawLsq hrawS
  have hψS : cellSum v (threeCycleInv v) S' ψ ≠ 0 := by
    have h₁ : cellSum v (threeCycleInv v) S' ψ = cellSum v (threeCycleInv v) S' w₁ := by
      rw [hψdef]
      refine cellSum_levelAvg_of_forall (v := v) hT₃ne (fun t ht => ?_)
      obtain ⟨y, hy, z, hz, rfl⟩ := hT₃shape t ht
      exact cellSum_minor_rightTranslate hw₁mem hS'tr hw₁L'
        (fun u hu => mul_mem_valuationBall (by omega) hu hy) (fun u hu => mul_mem_valuationBall (by omega) hu hy)
        (AddSubgroup.zero_mem _) (valuationBall_le_of_le v (by omega) hz)
    have h₂ : cellSum v (threeCycleInv v) S' w₁ = cellSum v (threeCycleInv v) S' (minorRawWord v) := by
      rw [hw₁def]
      refine cellSum_levelAvg_of_forall (v := v) hT₁ne (fun t ht => ?_)
      obtain ⟨a, ha, rfl⟩ := hT₁shape t ht
      exact cellSum_minor_rightTranslate hrawmem hS'tr hrawL' (fun _ _ => by simp) (fun _ _ => by simp)
        (valuationBall_le_of_le v (by omega) ha) (AddSubgroup.zero_mem _)
    rw [h₁, h₂]
    exact hrawS'

  refine apply_eq_zero_of_cellSum_ne_zero (v := v) Λ
    (U := upperUnipotentSubgroup v ⊤ ⊥ ⊤ (forall_mul_mem_bot_mem ⊤ ⊤))
    (K := upperUnipotentSubgroup v (valuationBall v (-(M₄ : ℤ))) ⊥ (valuationBall v (-(2 * (M₄ : ℤ))))
      (forall_mul_mem_bot_mem (valuationBall v (-(M₄ : ℤ))) (valuationBall v (-(2 * (M₄ : ℤ))))))
    (L := upperUnipotentSubgroup v (valuationBall v ((N₄ : ℤ) + M)) ⊥ (valuationBall v N₄)
      (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M)) (valuationBall v N₄)))
    (upperUnipotentSubgroup_le le_top le_rfl le_top) ?_ (Z := {g : LocalGL3 v | cornerEntry v g = 0})
    (Z' := {g : LocalGL3 v | cornerEntry v g * lowerMinor v g = 0}) ?_ (threeCycleInv v) ?_ hS'tr
    (fun h hh => h₅ h (fun g hg => hh g hg)) ⟨ψ, hψmem⟩ (fun g hg => hψZ g hg) ?_ ?_ hΛψ hψS f (fun g hg => hf g hg)
    ?_ ?_
  ·
    refine forall_mem_apply_rightTranslate_eq_of_forall_upperUnipotent3 (v := v) Λ hN (fun u hu => ?_)
    obtain ⟨x, y, z, -, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
    exact ⟨x, y, z, rfl⟩
  ·
    intro g hg u hu
    obtain ⟨x, y, z, -, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
    exact mem_setOf_cornerEntry_mul hg x y z
  ·
    intro h hh hZ hcell g hg
    refine apply_eq_zero_of_cornerEntry_mul_lowerMinor_eq_zero upperTriangularFactors hh (fun g' h20 => hZ g' h20)
      (fun u w => ?_) hg
    exact hcell (upperUnipotent3 u 0 w) (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
      ⟨AddSubgroup.mem_top _, AddSubgroup.mem_bot.2 rfl, AddSubgroup.mem_top _⟩)
  ·
    exact apply_mul_eq_of_mem_levelSubgroup hnψ (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))
  ·
    exact apply_threeCycleInv_mul_eq_zero_of_not_mem_box hmψ hmψM₄
  ·
    exact apply_mul_eq_of_mem_levelSubgroup hnf (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))
  ·
    exact apply_threeCycleInv_mul_eq_zero_of_not_mem_box hmf hmfM₄

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_WitnessLinks2

section JoinPiece_WitnessLinks3

open IsDedekindDomain NumberField NumberField.AdelicLevel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 halfModulus3_uniformizerUnit halfModulus3_one_uniformizerUnit_one halfModulus3_one_one_uniformizerUnit torusChar3 principalSeries3 isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul gl3Det_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul gl3Det_diagonal3_mul cellRatio antidiagonal3 antidiagonal3_coe eventually_norm_eq continuous_gl3Entry continuous_lowerMinor continuous_outerMinor continuous_gl3Det exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero valued_one_entry_le3 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 stepFunctions mem_stepFunctions_iff ballIndicator exists_valued_eq_exp one_lt_natCard_quot natCast_natCard_quot_ne_zero natCard_quot_eq_absNorm isCompact_setOf_valued_sub_le exists_setOf_valued_sub_le_subset_of_isOpen withZero_lt_one_iff_le_exp_neg_one exists_ball_representatives_add exists_finset_ball_representatives stepFunctions_le_span_ballIndicator sum_eq_sum_of_ball_representatives sum_eq_sum_of_ball_representatives_of_le ofReal_norm_eq_of_valued_eq ballIndicator_comp_mul_left exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace BruhatCells

variable {v : HeightOneSpectrum (𝓞 ℚ)}

variable (v) in

private noncomputable def openRawWord : LocalGL3 v → ℂ :=
  torusDifference v (secondTorusElement v) (minorRawWord v)

private theorem openRawWord_mem : openRawWord v ∈ principalSeries3 v fun _ => 1 :=
  torusDifference_mem_principalSeries3 v _ minorRawWord_mem

private theorem openRawWord_apply_eq_zero (g : LocalGL3 v) (h20 : cornerEntry v g = 0)
    (h : gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0) : openRawWord v g = 0 := by
  unfold openRawWord
  rcases mul_eq_zero.1 h with h10 | h21
  · exact torusDifference_apply_eq_zero_of_forall_secondClosure minorRawWord_apply_eq_zero _ g h20 h10
  · exact secondElementKillsFirstClosure minorRawWord_mem g h20 h21

private theorem cellSum_eq_sum_sum_sum_openCellProfile {X Y Z : Finset (v.adicCompletion ℚ)} {S : Finset (LocalGL3 v)}
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, g = upperUnipotent3 x y z) (f : LocalGL3 v → ℂ) :
    cellSum v (antidiagonal3 v) S f = ∑ x ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, openCellProfile v f x y z := by
  simp only [cellSum, openCellProfile, openCellPoint]
  exact sum_eq_sum_upperUnipotent3 (v := v) hS (fun s => f (antidiagonal3 v * s))

private theorem link5 (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)
    (hN : ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
    (hT : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f) :
    (∀ f : ↥(principalSeries3 v (fun _ => 1)), (∀ g : LocalGL3 v, (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0) →
      ∀ f : ↥(principalSeries3 v (fun _ => 1)),
        (∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → (f : LocalGL3 v → ℂ) g = 0) → Λ f = 0 := by
  intro h₆ f hf
  have hφ := sphericalSection3_mem v
  have hq : residueCardC v ≠ 0 := natCast_natCard_quot_ne_zero (v := v)
  have hq1 : residueCardC v ≠ 1 := by
    have := one_lt_natCard_quot (v := v)
    simp only [residueCardC, ne_eq, Nat.cast_eq_one]
    omega
  have hrawmem : openRawWord v ∈ principalSeries3 v fun _ => 1 := openRawWord_mem

  obtain ⟨n₀, hn₀⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ hrawmem
  obtain ⟨M₃, hM₃⟩ := cornerCellProfile_eq_zero_of_large hrawmem
    (fun g h20 h => openRawWord_apply_eq_zero g h20 h)
  obtain ⟨N₃, hN₃2, hn₀N₃⟩ : ∃ N₃ : ℕ, 2 ≤ N₃ ∧ n₀ ≤ N₃ := ⟨max n₀ 2, le_max_right _ _, le_max_left _ _⟩

  obtain ⟨Y, hY, hYmem, -, hYne⟩ := exists_system (v := v) (-(M₃ : ℤ)) N₃ (by omega)
  obtain ⟨Z, hZ, hZmem, hZ', hZne⟩ := exists_system (v := v) (-(2 * (M₃ : ℤ))) N₃ (by omega)
  obtain ⟨T₃, hT₃, hT₃tr⟩ := exists_transversal_of_systems (v := v)
    (forall_mem_bot_mul_mem (valuationBall v (-(M₃ : ℤ))) (valuationBall v (-(2 * (M₃ : ℤ)))))
    (forall_mem_bot_mul_mem (valuationBall v N₃) (valuationBall v N₃)) (valuationBall_le_of_le v (by omega))
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v))
    hY hYmem hZ hZmem
  have hT₃uni := forall_exists_eq_upperUnipotent3_of_forall_iff hT₃
  have hT₃ne := nonempty_of_forall_iff hT₃ singleton_zero_nonempty hYne hZne
  have hT₃shape : ∀ t ∈ T₃, ∃ y ∈ valuationBall v (-(M₃ : ℤ)), ∃ z ∈ valuationBall v (-(2 * (M₃ : ℤ))),
      t = upperUnipotent3 0 y z := by
    intro t ht
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := (hT₃ t).1 ht
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨y, hY y hy, z, hZ z hz, rfl⟩
  have hrawL₃ : ∀ κ ∈ upperUnipotentSubgroup v ⊥ (valuationBall v N₃) (valuationBall v N₃)
      (forall_mem_bot_mul_mem (valuationBall v N₃) (valuationBall v N₃)),
      ∀ g, openRawWord v (g * κ) = openRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ bot_le (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))
  have hcornerSum : cellSum v (threeCycle v) T₃ (openRawWord v) = 0 := by
    rw [cellSum_eq_sum_sum_cornerCellProfile hT₃]
    exact sum_sum_cornerCellProfile_word211_eq_zero (v := v) hφ (ky := -(M₃ : ℤ)) (kz := -(2 * (M₃ : ℤ)))
      (by omega) (by omega) hN₃2 (fun r hr => mem_valuationBall_iff.1 (hY r hr)) hZ'
  set w₁ : LocalGL3 v → ℂ := levelAvg v T₃ (openRawWord v) with hw₁def
  have hw₁mem : w₁ ∈ principalSeries3 v fun _ => 1 := levelAvg_mem_principalSeries3 v T₃ hrawmem
  have hw₁Z : ∀ g : LocalGL3 v, cornerEntry v g = 0 → w₁ g = 0 := by
    intro g hg
    refine apply_eq_zero_of_cornerEntry_eq_zero upperTriangularFactors hw₁mem
      (fun g' h20 h' => levelAvg_apply_eq_zero_of_forall_lengthLeOne hT₃uni openRawWord_apply_eq_zero g' h20 h')
      (fun y z => ?_) hg
    rw [hw₁def]
    by_cases hu : (upperUnipotent3 0 y z : LocalGL3 v) ∈ upperUnipotentSubgroup v ⊥ (valuationBall v (-(M₃ : ℤ)))
        (valuationBall v (-(2 * (M₃ : ℤ)))) (forall_mem_bot_mul_mem _ _)
    · rw [levelAvg_apply_mul_of_mem (v := v) hT₃tr hrawL₃ (threeCycle v) hu, hcornerSum, mul_zero]
    · exact levelAvg_apply_mul_of_not_mem (v := v)
        (U := upperUnipotentSubgroup v ⊥ ⊤ ⊤ (forall_mem_bot_mul_mem ⊤ ⊤))
        (upperUnipotentSubgroup_le le_rfl le_top le_top) hT₃tr.1
        (apply_threeCycle_mul_eq_zero_of_not_mem hM₃ le_rfl)
        (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
          ⟨AddSubgroup.mem_bot.2 rfl, AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩) hu

  obtain ⟨n₁, hn₁⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ hw₁mem
  obtain ⟨m₁, hm₁⟩ := minorCellProfile_eq_zero_of_large hw₁mem hw₁Z
  obtain ⟨M₄, hM₃M₄, hm₁M₄⟩ : ∃ M₄ : ℕ, M₃ ≤ M₄ ∧ m₁ ≤ M₄ := ⟨max M₃ m₁, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨N₄, hN₃N₄, hn₁N₄⟩ : ∃ N₄ : ℕ, N₃ ≤ N₄ ∧ n₁ ≤ N₄ := ⟨max N₃ n₁, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨U', hU', hU'mem, -, hU'ne⟩ := exists_system (v := v) (-(M₄ : ℤ)) ((N₄ : ℤ) + M₃) (by omega)
  obtain ⟨U, hU, hUmem, hU'', -⟩ := exists_system (v := v) (-(M₄ : ℤ)) N₄ (by omega)
  obtain ⟨W, hW, hWmem, hW'', hWne⟩ := exists_system (v := v) (-(2 * (M₄ : ℤ))) N₄ (by omega)
  obtain ⟨R, hR, hRmem, -, -⟩ := exists_system (v := v) N₄ ((N₄ : ℤ) + M₃) (by omega)
  obtain ⟨W₀, hW₀, hW₀mem, -, -⟩ := exists_system (v := v) N₄ N₄ le_rfl
  obtain ⟨T₄, hT₄, hT₄tr⟩ := exists_transversal_of_systems (v := v)
    (forall_mul_mem_bot_mem (valuationBall v (-(M₄ : ℤ))) (valuationBall v (-(2 * (M₄ : ℤ)))))
    (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M₃)) (valuationBall v N₄)) le_rfl hU' hU'mem
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v)) hW hWmem
  obtain ⟨S₄, hS₄, hS₄tr⟩ := exists_transversal_of_systems (v := v)
    (forall_mul_mem_bot_mem (valuationBall v (-(M₄ : ℤ))) (valuationBall v (-(2 * (M₄ : ℤ)))))
    (forall_mul_mem_bot_mem (valuationBall v N₄) (valuationBall v N₄)) le_rfl hU hUmem
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v)) hW hWmem
  obtain ⟨Q₄, -, hQ₄tr⟩ := exists_transversal_of_systems (v := v)
    (forall_mul_mem_bot_mem (valuationBall v N₄) (valuationBall v N₄))
    (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M₃)) (valuationBall v N₄)) le_rfl hR hRmem
    (forall_mem_singleton_zero_mem_bot (v := v)) (existsUnique_mem_singleton_zero_of_mem_bot (v := v)) hW₀ hW₀mem
  have hT₄uni := forall_exists_eq_upperUnipotent3_of_forall_iff hT₄
  have hT₄ne := nonempty_of_forall_iff hT₄ hU'ne singleton_zero_nonempty hWne
  have hT₄shape : ∀ t ∈ T₄, ∃ a ∈ valuationBall v (-(M₄ : ℤ)), ∃ c ∈ valuationBall v (-(2 * (M₄ : ℤ))),
      t = upperUnipotent3 a 0 c := by
    intro t ht
    obtain ⟨a, ha, y, hy, c, hc, rfl⟩ := (hT₄ t).1 ht
    rw [Finset.mem_singleton] at hy
    subst hy
    exact ⟨a, hU' a ha, c, hW c hc, rfl⟩
  have hrawL₄ : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v ((N₄ : ℤ) + M₃)) ⊥ (valuationBall v N₄)
      (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M₃)) (valuationBall v N₄)),
      ∀ g, openRawWord v (g * κ) = openRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))
  have hrawL₄sq : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v N₄) ⊥ (valuationBall v N₄)
      (forall_mul_mem_bot_mem (valuationBall v N₄) (valuationBall v N₄)),
      ∀ g, openRawWord v (g * κ) = openRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))
  have hw₁L₄ : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v ((N₄ : ℤ) + M₃)) ⊥ (valuationBall v N₄)
      (forall_mul_mem_bot_mem (valuationBall v ((N₄ : ℤ) + M₃)) (valuationBall v N₄)), ∀ g, w₁ (g * κ) = w₁ g :=
    apply_mul_eq_of_mem_levelSubgroup hn₁ (valuationBall_le_of_le v (by omega)) bot_le
      (valuationBall_le_of_le v (by omega))

  have hminorSq : cellSum v (threeCycleInv v) S₄ (openRawWord v) = 0 := by
    rw [cellSum_eq_sum_sum_minorCellProfile hS₄]
    exact sum_sum_minorCellProfile_word211_eq_zero (v := v) hφ (ku := -(M₄ : ℤ)) (kw := -(2 * (M₄ : ℤ))) (by omega)
      (by omega) (N := N₄) (by omega) hU'' hW''
  have hminorRaw : cellSum v (threeCycleInv v) T₄ (openRawWord v) = 0 := by
    rw [cellSum_eq_card_mul_cellSum (v := v)
      (upperUnipotentSubgroup_le (valuationBall_le_of_le v (by omega)) le_rfl (valuationBall_le_of_le v (by omega)))
      (upperUnipotentSubgroup_le (valuationBall_le_of_le v (by omega)) le_rfl le_rfl) hT₄tr hS₄tr hQ₄tr
      (threeCycleInv v) hrawL₄sq, hminorSq, mul_zero]
  have hminorSum : cellSum v (threeCycleInv v) T₄ w₁ = 0 := by
    have h : cellSum v (threeCycleInv v) T₄ w₁ = cellSum v (threeCycleInv v) T₄ (openRawWord v) := by
      rw [hw₁def]
      refine cellSum_levelAvg_of_forall (v := v) hT₃ne (fun t ht => ?_)
      obtain ⟨y, hy, z, hz, rfl⟩ := hT₃shape t ht
      exact cellSum_minor_rightTranslate hrawmem hT₄tr hrawL₄
        (fun u hu => mul_mem_valuationBall (by omega) hu hy) (fun u hu => mul_mem_valuationBall (by omega) hu hy)
        (AddSubgroup.zero_mem _) (valuationBall_le_of_le v (by omega) hz)
    rw [h, hminorRaw]
  set ψ : LocalGL3 v → ℂ := levelAvg v T₄ w₁ with hψdef
  have hψmem : ψ ∈ principalSeries3 v fun _ => 1 := levelAvg_mem_principalSeries3 v T₄ hw₁mem
  have hψZ : ∀ g : LocalGL3 v, cornerEntry v g * lowerMinor v g = 0 → ψ g = 0 := by
    intro g hg
    refine apply_eq_zero_of_cornerEntry_mul_lowerMinor_eq_zero upperTriangularFactors hψmem
      (fun g' h20 => levelAvg_apply_eq_zero_of_forall_cornerEntry hT₄uni hw₁Z g' h20) (fun u w => ?_) hg
    rw [hψdef]
    by_cases hu : (upperUnipotent3 u 0 w : LocalGL3 v) ∈ upperUnipotentSubgroup v (valuationBall v (-(M₄ : ℤ))) ⊥
        (valuationBall v (-(2 * (M₄ : ℤ)))) (forall_mul_mem_bot_mem _ _)
    · rw [levelAvg_apply_mul_of_mem (v := v) hT₄tr hw₁L₄ (threeCycleInv v) hu, hminorSum, mul_zero]
    · exact levelAvg_apply_mul_of_not_mem (v := v)
        (U := upperUnipotentSubgroup v ⊤ ⊥ ⊤ (forall_mul_mem_bot_mem ⊤ ⊤))
        (upperUnipotentSubgroup_le le_top le_rfl le_top) hT₄tr.1
        (apply_threeCycleInv_mul_eq_zero_of_not_mem_box hm₁ hm₁M₄)
        (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
          ⟨AddSubgroup.mem_top _, AddSubgroup.mem_bot.2 rfl, AddSubgroup.mem_top _⟩) hu

  have hΛψ : Λ ⟨ψ, hψmem⟩ = 0 := by
    have e₁ := apply_levelAvg_eq (v := v) Λ hN hT₄ne hT₄uni ⟨w₁, hw₁mem⟩
    have e₂ := apply_levelAvg_eq (v := v) Λ hN hT₃ne hT₃uni ⟨openRawWord v, hrawmem⟩
    have e₃ := apply_torusDifference_eq_zero (v := v) Λ hT (secondTorusElement v) ⟨minorRawWord v, minorRawWord_mem⟩
    exact e₁.trans (e₂.trans e₃)

  obtain ⟨mψ, hmψ⟩ := openCellProfile_eq_zero_of_large hψmem hψZ
  obtain ⟨mf, hmf⟩ := openCellProfile_eq_zero_of_large f.2 hf
  obtain ⟨nψ, hnψ⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ hψmem
  obtain ⟨nf, hnf⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v _ _ f.2
  obtain ⟨M₅, hM₅1, hM₄M₅, hmψM₅, hmfM₅⟩ : ∃ M₅ : ℕ, 1 ≤ M₅ ∧ M₄ ≤ M₅ ∧ mψ ≤ M₅ ∧ mf ≤ M₅ :=
    ⟨max (max 1 M₄) (max mψ mf), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨N₅, hN₅2, hN₄N₅, hnψN₅, hnfN₅⟩ : ∃ N₅ : ℕ, 2 ≤ N₅ ∧ N₄ ≤ N₅ ∧ nψ ≤ N₅ ∧ nf ≤ N₅ :=
    ⟨max (max 2 N₄) (max nψ nf), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hKbox : ∀ x ∈ valuationBall v (-(M₅ : ℤ)), ∀ y ∈ valuationBall v (-(M₅ : ℤ)),
      x * y ∈ valuationBall v (-(2 * (M₅ : ℤ))) :=
    fun _ hx _ hy => mul_mem_valuationBall (by omega) hx hy
  have hLsq : ∀ x ∈ valuationBall v N₅, ∀ y ∈ valuationBall v N₅, x * y ∈ valuationBall v N₅ :=
    fun _ hx _ hy => mul_mem_valuationBall (by omega) hx hy
  have hLrect : ∀ x ∈ valuationBall v ((N₅ : ℤ) + M₃), ∀ y ∈ valuationBall v ((N₅ : ℤ) + M₄),
      x * y ∈ valuationBall v N₅ :=
    fun _ hx _ hy => mul_mem_valuationBall (by omega) hx hy
  obtain ⟨X₅, hX₅, hX₅mem, hX₅', -⟩ := exists_system (v := v) (-(M₅ : ℤ)) N₅ (by omega)
  obtain ⟨Y₅, hY₅, hY₅mem, hY₅', -⟩ := exists_system (v := v) (-(M₅ : ℤ)) N₅ (by omega)
  obtain ⟨Z₅, hZ₅, hZ₅mem, hZ₅', -⟩ := exists_system (v := v) (-(2 * (M₅ : ℤ))) N₅ (by omega)
  obtain ⟨X₅', hX₅'', hX₅'mem, -, -⟩ := exists_system (v := v) (-(M₅ : ℤ)) ((N₅ : ℤ) + M₃) (by omega)
  obtain ⟨Y₅', hY₅'', hY₅'mem, -, -⟩ := exists_system (v := v) (-(M₅ : ℤ)) ((N₅ : ℤ) + M₄) (by omega)
  obtain ⟨RX, hRX, hRXmem, -, -⟩ := exists_system (v := v) N₅ ((N₅ : ℤ) + M₃) (by omega)
  obtain ⟨RY, hRY, hRYmem, -, -⟩ := exists_system (v := v) N₅ ((N₅ : ℤ) + M₄) (by omega)
  obtain ⟨RZ, hRZ, hRZmem, -, -⟩ := exists_system (v := v) N₅ N₅ le_rfl
  obtain ⟨S₅, hS₅, hS₅tr⟩ := exists_transversal_of_systems (v := v) hKbox hLsq (valuationBall_le_of_le v (by omega))
    hX₅ hX₅mem hY₅ hY₅mem hZ₅ hZ₅mem
  obtain ⟨S₅', -, hS₅'tr⟩ := exists_transversal_of_systems (v := v) hKbox hLrect (valuationBall_le_of_le v (by omega))
    hX₅'' hX₅'mem hY₅'' hY₅'mem hZ₅ hZ₅mem
  obtain ⟨Q₅, -, hQ₅tr⟩ := exists_transversal_of_systems (v := v) hLsq hLrect (valuationBall_le_of_le v (by omega))
    hRX hRXmem hRY hRYmem hRZ hRZmem
  have hrawL₅sq : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v N₅) (valuationBall v N₅) (valuationBall v N₅) hLsq,
      ∀ g, openRawWord v (g * κ) = openRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ (valuationBall_le_of_le v (by omega)) (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))
  have hrawL₅ : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v ((N₅ : ℤ) + M₃)) (valuationBall v ((N₅ : ℤ) + M₄))
      (valuationBall v N₅) hLrect, ∀ g, openRawWord v (g * κ) = openRawWord v g :=
    apply_mul_eq_of_mem_levelSubgroup hn₀ (valuationBall_le_of_le v (by omega)) (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))
  have hw₁L₅ : ∀ κ ∈ upperUnipotentSubgroup v (valuationBall v ((N₅ : ℤ) + M₃)) (valuationBall v ((N₅ : ℤ) + M₄))
      (valuationBall v N₅) hLrect, ∀ g, w₁ (g * κ) = w₁ g :=
    apply_mul_eq_of_mem_levelSubgroup hn₁ (valuationBall_le_of_le v (by omega)) (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega))

  have hrawS : cellSum v (antidiagonal3 v) S₅ (openRawWord v) ≠ 0 := by
    rw [cellSum_eq_sum_sum_sum_openCellProfile hS₅]
    show (∑ x ∈ X₅, ∑ y ∈ Y₅, ∑ z ∈ Z₅, openCellProfile v (torusDifference v (secondTorusElement v)
      (torusDifference v (firstTorusElement v) (torusDifference v (firstTorusElement v) (sphericalSection3 v))))
        x y z) ≠ 0
    rw [sum_sum_sum_openCellProfile_word_sphericalSection3 (v := v) (kx := -(M₅ : ℤ)) (ky := -(M₅ : ℤ))
      (kz := -(2 * (M₅ : ℤ))) (by omega) le_rfl (by omega) (by omega) hN₅2
      (fun r hr => mem_valuationBall_iff.1 (hX₅ r hr)) hX₅' (fun r hr => mem_valuationBall_iff.1 (hY₅ r hr)) hY₅'
      (fun r hr => mem_valuationBall_iff.1 (hZ₅ r hr)) hZ₅']
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hq1)) (pow_ne_zero _ hq)
  have hrawS' : cellSum v (antidiagonal3 v) S₅' (openRawWord v) ≠ 0 :=
    cellSum_ne_zero_of_refine (v := v)
      (upperUnipotentSubgroup_le (valuationBall_le_of_le v (by omega)) (valuationBall_le_of_le v (by omega))
        (valuationBall_le_of_le v (by omega)))
      (upperUnipotentSubgroup_le (valuationBall_le_of_le v (by omega)) (valuationBall_le_of_le v (by omega)) le_rfl)
      hS₅'tr hS₅tr hQ₅tr (antidiagonal3 v) hrawL₅sq hrawS
  have hψS : cellSum v (antidiagonal3 v) S₅' ψ ≠ 0 := by
    have h₁ : cellSum v (antidiagonal3 v) S₅' ψ = cellSum v (antidiagonal3 v) S₅' w₁ := by
      rw [hψdef]
      refine cellSum_levelAvg_of_forall (v := v) hT₄ne (fun t ht => ?_)
      obtain ⟨a, ha, c, hc, rfl⟩ := hT₄shape t ht
      exact cellSum_open_rightTranslate hw₁mem hS₅'tr hw₁L₅
        (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
          ⟨valuationBall_le_of_le v (by omega) ha, AddSubgroup.zero_mem _, valuationBall_le_of_le v (by omega) hc⟩)
        (fun _ _ => by simp) (fun y hy => mul_mem_valuationBall (by omega) ha hy) (antidiagonal3 v)
    have h₂ : cellSum v (antidiagonal3 v) S₅' w₁ = cellSum v (antidiagonal3 v) S₅' (openRawWord v) := by
      rw [hw₁def]
      refine cellSum_levelAvg_of_forall (v := v) hT₃ne (fun t ht => ?_)
      obtain ⟨y, hy, z, hz, rfl⟩ := hT₃shape t ht
      exact cellSum_open_rightTranslate hrawmem hS₅'tr hrawL₅
        (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
          ⟨AddSubgroup.zero_mem _, valuationBall_le_of_le v (by omega) hy, valuationBall_le_of_le v (by omega) hz⟩)
        (fun x hx => mul_mem_valuationBall (by omega) hx hy) (fun _ _ => by simp) (antidiagonal3 v)
    rw [h₁, h₂]
    exact hrawS'

  refine apply_eq_zero_of_cellSum_ne_zero (v := v) Λ
    (U := upperUnipotentSubgroup v ⊤ ⊤ ⊤ (fun _ _ _ _ => AddSubgroup.mem_top _))
    (K := upperUnipotentSubgroup v (valuationBall v (-(M₅ : ℤ))) (valuationBall v (-(M₅ : ℤ)))
      (valuationBall v (-(2 * (M₅ : ℤ)))) hKbox)
    (L := upperUnipotentSubgroup v (valuationBall v ((N₅ : ℤ) + M₃)) (valuationBall v ((N₅ : ℤ) + M₄))
      (valuationBall v N₅) hLrect)
    (upperUnipotentSubgroup_le le_top le_top le_top) ?_
    (Z := {g : LocalGL3 v | cornerEntry v g * lowerMinor v g = 0}) (Z' := Set.univ) ?_ (antidiagonal3 v) ?_ hS₅'tr
    (fun h hh => h₆ h (fun g => hh g (Set.mem_univ g))) ⟨ψ, hψmem⟩ (fun g hg => hψZ g hg) ?_ ?_ hΛψ hψS f
    (fun g hg => hf g hg) ?_ ?_
  · refine forall_mem_apply_rightTranslate_eq_of_forall_upperUnipotent3 (v := v) Λ hN (fun u hu => ?_)
    obtain ⟨x, y, z, -, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
    exact ⟨x, y, z, rfl⟩
  · intro g hg u hu
    obtain ⟨x, y, z, -, -, -, rfl⟩ := mem_upperUnipotentSubgroup_iff.1 hu
    exact mem_setOf_mul_lowerMinor_mul hg x y z
  · intro h hh hZ hcell g _
    refine apply_eq_zero_of_forall_openCell upperTriangularFactors hh (fun g' hg' => hZ g' hg') (fun x y z => ?_) g
    exact hcell (upperUnipotent3 x y z) (upperUnipotent3_mem_upperUnipotentSubgroup_iff.2
      ⟨AddSubgroup.mem_top _, AddSubgroup.mem_top _, AddSubgroup.mem_top _⟩)
  · exact apply_mul_eq_of_mem_levelSubgroup hnψ (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega)) (valuationBall_le_of_le v (by omega))
  · exact apply_antidiagonal3_mul_eq_zero_of_not_mem hmψ hmψM₅
  · exact apply_mul_eq_of_mem_levelSubgroup hnf (valuationBall_le_of_le v (by omega))
      (valuationBall_le_of_le v (by omega)) (valuationBall_le_of_le v (by omega))
  · exact apply_antidiagonal3_mul_eq_zero_of_not_mem hmf hmfM₅

end BruhatCells

end LanglandsTunnell.CubicInduction

end JoinPiece_WitnessLinks3

end

open IsDedekindDomain NumberField

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one.LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (s : Finset (↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)) :
    (∀ Λ ∈ s, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f) →
    (∀ Λ ∈ s, ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f) →
    (LinearIndependent ℂ (fun Λ : ↥s => (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ))) →
    s.card ≤ 1 := by
  intro hN hT hind
  exact card_le_one_of_forall_apply_eq_zero v s
    (fun Λ hΛ => forall_apply_eq_zero_of_chain v Λ
      (apply_eq_zero_of_vanishing_on_triangular v Λ (hN Λ hΛ) (hT Λ hΛ))
      (apply_eq_zero_of_vanishing_on_parabolic v Λ (hN Λ hΛ) (hT Λ hΛ))
      (BruhatCells.link3 Λ (hN Λ hΛ) (hT Λ hΛ))
      (BruhatCells.link4 Λ (hN Λ hΛ) (hT Λ hΛ))
      (BruhatCells.link5 Λ (hN Λ hΛ) (hT Λ hΛ)))
    hind

end S_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one (solution)
