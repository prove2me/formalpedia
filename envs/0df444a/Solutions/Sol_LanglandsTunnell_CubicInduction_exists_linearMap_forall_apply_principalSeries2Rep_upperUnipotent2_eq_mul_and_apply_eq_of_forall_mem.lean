-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4ead8079-b24b-50e0-9ab7-fb0f18c8eeb8

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

noncomputable section

namespace WhittakerPS2Ext

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Matrix Topology Filter

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def lowerUnip (y : F) : G where
  val := !![1, 0; y, 1]
  inv := !![1, 0; -y, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem lowerUnip_coe (y : F) : ((lowerUnip p y : G) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; y, 1] := rfl

theorem continuous_lowerUnip : Continuous (lowerUnip p) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnip] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnip] <;> fun_prop

theorem continuous_upperUnipotent2 : Continuous (upperUnipotent2 p) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2] <;> fun_prop

theorem diagonal2_coe' (a : Fin 2 → Fˣ) :
    ((diagonal2 p a : G) : Matrix (Fin 2) (Fin 2) F) = !![(a 0 : F), 0; 0, (a 1 : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_upper_diag_lower (x : F) (a : Fin 2 → Fˣ) (y : F) :
    ((upperUnipotent2 p x * diagonal2 p a * lowerUnip p y : G) : Matrix (Fin 2) (Fin 2) F)
      = !![(a 0 : F) + x * (a 1 : F) * y, x * (a 1 : F); (a 1 : F) * y, (a 1 : F)] := by
  rw [Units.val_mul, Units.val_mul, upperUnipotent2_coe, diagonal2_coe', lowerUnip_coe, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_upper_diag_lower_weyl (x : F) (a : Fin 2 → Fˣ) (y : F) :
    ((upperUnipotent2 p x * diagonal2 p a * (lowerUnip p y * antidiagonal2 p) : G) : Matrix (Fin 2) (Fin 2) F)
      = !![x * (a 1 : F), (a 0 : F) + x * (a 1 : F) * y; (a 1 : F), (a 1 : F) * y] := by
  rw [Units.val_mul, Units.val_mul, Units.val_mul, upperUnipotent2_coe, diagonal2_coe', lowerUnip_coe,
    antidiagonal2_coe, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem iwasawa (g : G) : ∃ (x : F) (a : Fin 2 → Fˣ) (y : F), Valued.v y ≤ 1 ∧
    (g = upperUnipotent2 p x * diagonal2 p a * lowerUnip p y ∨
      g = upperUnipotent2 p x * diagonal2 p a * (lowerUnip p y * antidiagonal2 p)) := by
  set A : F := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with hA
  set B : F := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hB
  set Cc : F := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hC
  set D : F := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hD
  have hdet : A * D - B * Cc ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
    exact h
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![A, B; Cc, D] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  by_cases hcd : Valued.v Cc ≤ Valued.v D
  · have hD0 : D ≠ 0 := by
      intro h0
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at hcd
      apply hdet
      rw [h0, hcd]
      ring
    have hα : (A * D - B * Cc) / D ≠ 0 := div_ne_zero hdet hD0
    refine ⟨B / D, ![Units.mk0 _ hα, Units.mk0 D hD0], Cc / D, ?_, Or.inl ?_⟩
    · rw [map_div₀]
      exact div_le_one_of_le₀ hcd zero_le'
    · apply Units.ext
      rw [hg, coe_upper_diag_lower]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring
  · push Not at hcd
    have hC0 : Cc ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hcd
      exact not_lt_zero hcd
    have hα : -(A * D - B * Cc) / Cc ≠ 0 := div_ne_zero (neg_ne_zero.mpr hdet) hC0
    refine ⟨A / Cc, ![Units.mk0 _ hα, Units.mk0 Cc hC0], D / Cc, ?_, Or.inr ?_⟩
    · rw [map_div₀]
      exact div_le_one_of_le₀ hcd.le zero_le'
    · apply Units.ext
      rw [hg, coe_upper_diag_lower_weyl]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

def iwasawaSet : Set G :=
  (lowerUnip p) '' (p.adicCompletionIntegers ℚ : Set F) ∪
    (fun y => lowerUnip p y * antidiagonal2 p) '' (p.adicCompletionIntegers ℚ : Set F)

theorem isCompact_iwasawaSet : IsCompact (iwasawaSet p) := by
  have hO : IsCompact (p.adicCompletionIntegers ℚ : Set F) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (p.adicCompletionIntegers ℚ)))
  exact (hO.image (continuous_lowerUnip p)).union
    (hO.image ((continuous_lowerUnip p).mul continuous_const))

theorem iwasawa' (g : G) : ∃ (x : F) (a : Fin 2 → Fˣ), ∃ k ∈ iwasawaSet p,
    g = upperUnipotent2 p x * diagonal2 p a * k := by
  obtain ⟨x, a, y, hy, h⟩ := iwasawa p g
  have hy' : y ∈ (p.adicCompletionIntegers ℚ : Set F) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hy
  rcases h with h | h
  · exact ⟨x, a, lowerUnip p y, Or.inl ⟨y, hy', rfl⟩, h⟩
  · exact ⟨x, a, lowerUnip p y * antidiagonal2 p, Or.inr ⟨y, hy', rfl⟩, h⟩

variable (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

theorem law {f : G → ℂ} (hf : f ∈ principalSeries2 p χ) (x : F) (a : Fin 2 → Fˣ) (g : G) :
    f (upperUnipotent2 p x * diagonal2 p a * g) = torusChar2 p χ a * halfModulus2 p a * f g := by
  obtain ⟨-, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  rw [mul_assoc, hn, ht]

theorem rho_apply (g : G) (f : ↥(principalSeries2 p χ)) (h : G) :
    ((principalSeries2Rep χ g f : ↥(principalSeries2 p χ)) : G → ℂ) h = (f : G → ℂ) (h * g) := rfl

theorem rho_mul (g g' : G) (f : ↥(principalSeries2 p χ)) :
    principalSeries2Rep χ (g * g') f = principalSeries2Rep χ g (principalSeries2Rep χ g' f) := by
  rw [map_mul]
  rfl

theorem exists_forall_rho_upper_eq (f : ↥(principalSeries2 p χ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : F, ‖y‖ ≤ ε → principalSeries2Rep χ (upperUnipotent2 p y) f = f := by
  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp f.2

  have hcont : Continuous fun q : G × F => q.1 * upperUnipotent2 p q.2 :=
    continuous_fst.mul ((continuous_upperUnipotent2 p).comp continuous_snd)
  have hΦlc : IsLocallyConstant fun q : G × F => (f : G → ℂ) (q.1 * upperUnipotent2 p q.2) :=
    hlc.comp_continuous hcont
  have hloc : ∀ k₀ : G, ∃ W : Set G, IsOpen W ∧ k₀ ∈ W ∧ ∃ ε > 0,
      ∀ k ∈ W, ∀ y : F, ‖y‖ < ε → (f : G → ℂ) (k * upperUnipotent2 p y) = (f : G → ℂ) k := by
    intro k₀
    obtain ⟨O, hOopen, hk₀O, hOconst⟩ := hΦlc.exists_open (k₀, (0 : F))
    obtain ⟨W, V, hW, hV, hkW, h0V, hWV⟩ := isOpen_prod_iff.mp hOopen k₀ 0 hk₀O
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
    refine ⟨W, hW, hkW, ε, hε, fun k hk y hy => ?_⟩
    have hyV : y ∈ V := hball (by rwa [Metric.mem_ball, dist_zero_right])
    have h1 := hOconst (k, y) (hWV (Set.mk_mem_prod hk hyV))
    have h2 := hOconst (k, (0 : F)) (hWV (Set.mk_mem_prod hk h0V))
    simp only [upperUnipotent2_zero, mul_one] at h1 h2
    rw [h1, h2]
  choose W hWopen hkW eps heps hWconst using hloc
  obtain ⟨t, -, htcov⟩ := (isCompact_iwasawaSet p).elim_nhds_subcover W (fun k _ => (hWopen k).mem_nhds (hkW k))

  have hε : ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ t, ε < eps k := by
    by_cases ht : t.Nonempty
    · refine ⟨t.inf' ht eps / 2, ?_, fun k hk => ?_⟩
      · have : 0 < t.inf' ht eps := by
          rw [Finset.lt_inf'_iff]
          intro k _
          exact heps k
        linarith
      · have h1 : t.inf' ht eps ≤ eps k := Finset.inf'_le _ hk
        have h2 : 0 < eps k := heps k
        linarith
    · refine ⟨1, one_pos, fun k hk => ?_⟩
      exact absurd ⟨k, hk⟩ ht
  obtain ⟨ε, hεpos, hεlt⟩ := hε
  refine ⟨ε, hεpos, fun y hy => ?_⟩
  apply Subtype.ext
  funext g
  rw [rho_apply]
  obtain ⟨x, a, k, hkC, rfl⟩ := iwasawa' p g
  have hk := htcov hkC
  rw [Set.mem_iUnion₂] at hk
  obtain ⟨k₁, hk₁t, hkW₁⟩ := hk
  rw [mul_assoc (upperUnipotent2 p x * diagonal2 p a), law p χ f.2, law p χ f.2,
    hWconst k₁ k hkW₁ y (lt_of_le_of_lt hy (hεlt k₁ hk₁t))]

def IsTame (ψ : AddChar F ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ y : F, ‖y‖ ≤ δ → ψ y = 1

theorem psi_neg_mul_self (ψ : AddChar F ℂ) (a : F) : ψ (-a) * ψ a = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem psi_ne_zero (ψ : AddChar F ℂ) (a : F) : ψ a ≠ 0 := fun h => by
  have := psi_neg_mul_self p ψ a
  rw [h, mul_zero] at this
  exact zero_ne_one this

structure IsPart (R r : ℝ) (T : Finset F) : Prop where
  inside : ∀ a ∈ T, ‖a‖ ≤ R
  cover : ∀ x : F, ‖x‖ ≤ R → ∃ a ∈ T, ‖x - a‖ ≤ r
  sep : ∀ a ∈ T, ∀ b ∈ T, ‖a - b‖ ≤ r → a = b

theorem norm_sub_le_of_le_of_le {x y z : F} {r : ℝ} (h1 : ‖x - y‖ ≤ r) (h2 : ‖y - z‖ ≤ r) : ‖x - z‖ ≤ r := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h1 h2)

theorem exists_isPart {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) : ∃ T : Finset F, IsPart p R r T ∧ T.Nonempty := by
  classical

  obtain ⟨T₀, hT₀S, hT₀cov⟩ := (isCompact_closedBall (0 : F) R).elim_nhds_subcover
    (fun a => Metric.closedBall a r)
    (fun a _ => (IsUltrametricDist.isOpen_closedBall a (ne_of_gt hr)).mem_nhds
      (Metric.mem_closedBall_self (le_of_lt hr)))
  have hcov₀ : ∀ x : F, ‖x‖ ≤ R → ∃ a ∈ T₀, ‖x - a‖ ≤ r := by
    intro x hx
    have hxS : x ∈ Metric.closedBall (0 : F) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx
    have hmem := hT₀cov hxS
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨a, haT, hxa⟩ := hmem
    rw [Metric.mem_closedBall, dist_eq_norm] at hxa
    exact ⟨a, haT, hxa⟩
  have hin₀ : ∀ a ∈ T₀, ‖a‖ ≤ R := by
    intro a ha
    have := hT₀S a ha
    rwa [Metric.mem_closedBall, dist_zero_right] at this

  set ι : F → ℕ := fun a => if h : a ∈ T₀ then (T₀.equivFin ⟨a, h⟩ : ℕ) else 0 with hι
  have hιinj : ∀ a ∈ T₀, ∀ b ∈ T₀, ι a = ι b → a = b := by
    intro a ha b hb hab
    simp only [hι, dif_pos ha, dif_pos hb] at hab
    have := T₀.equivFin.injective (Fin.ext hab)
    exact congrArg Subtype.val this
  set T : Finset F := T₀.filter (fun a => ∀ b ∈ T₀, ‖b - a‖ ≤ r → ι a ≤ ι b) with hT
  refine ⟨T, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a ha
    exact hin₀ a (Finset.mem_filter.mp ha).1
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := hcov₀ x hx

    set Cl : Finset F := T₀.filter (fun c => ‖c - b‖ ≤ r) with hCl
    have hbCl : b ∈ Cl := by
      rw [hCl, Finset.mem_filter, sub_self, norm_zero]
      exact ⟨hb, le_of_lt hr⟩
    obtain ⟨c₀, hc₀Cl, hc₀min⟩ := Cl.exists_min_image ι ⟨b, hbCl⟩
    obtain ⟨hc₀T₀, hc₀b⟩ := Finset.mem_filter.mp hc₀Cl
    refine ⟨c₀, ?_, ?_⟩
    · rw [hT, Finset.mem_filter]
      refine ⟨hc₀T₀, fun b' hb' hb'c₀ => hc₀min b' ?_⟩
      rw [hCl, Finset.mem_filter]
      exact ⟨hb', norm_sub_le_of_le_of_le p hb'c₀ hc₀b⟩
    · have : ‖b - c₀‖ ≤ r := by rw [norm_sub_rev]; exact hc₀b
      exact norm_sub_le_of_le_of_le p hxb this
  · intro a ha b hb hab
    obtain ⟨haT₀, hamin⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbT₀, hbmin⟩ := Finset.mem_filter.mp hb
    have h1 : ι a ≤ ι b := hamin b hbT₀ (by rw [norm_sub_rev]; exact hab)
    have h2 : ι b ≤ ι a := hbmin a haT₀ hab
    exact hιinj a haT₀ b hbT₀ (le_antisymm h1 h2)
  · obtain ⟨b, hb, _⟩ := hcov₀ 0 (by rw [norm_zero]; exact hR)
    set Cl : Finset F := T₀.filter (fun c => ‖c - b‖ ≤ r) with hCl
    have hbCl : b ∈ Cl := by
      rw [hCl, Finset.mem_filter, sub_self, norm_zero]
      exact ⟨hb, le_of_lt hr⟩
    obtain ⟨c₀, hc₀Cl, hc₀min⟩ := Cl.exists_min_image ι ⟨b, hbCl⟩
    obtain ⟨hc₀T₀, hc₀b⟩ := Finset.mem_filter.mp hc₀Cl
    refine ⟨c₀, ?_⟩
    rw [hT, Finset.mem_filter]
    refine ⟨hc₀T₀, fun b' hb' hb'c₀ => hc₀min b' ?_⟩
    rw [hCl, Finset.mem_filter]
    exact ⟨hb', norm_sub_le_of_le_of_le p hb'c₀ hc₀b⟩

theorem exists_perm_of_isPart {R r : ℝ} {T : Finset F} (hT : IsPart p R r T) (_hrR : r ≤ R) {s : F}
    (hs : ‖s‖ ≤ R) :
    ∃ σ : F → F, (∀ a ∈ T, σ a ∈ T) ∧ (∀ a ∈ T, ‖a + s - σ a‖ ≤ r) ∧
      (∀ a ∈ T, ∀ b ∈ T, σ a = σ b → a = b) := by
  classical
  have hex : ∀ a ∈ T, ∃ a' ∈ T, ‖a + s - a'‖ ≤ r := by
    intro a ha
    exact hT.cover (a + s) (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (hT.inside a ha) hs))
  refine ⟨fun a => if h : a ∈ T then (hex a h).choose else a, ?_, ?_, ?_⟩
  · intro a ha
    simp only [dif_pos ha]
    exact (hex a ha).choose_spec.1
  · intro a ha
    simp only [dif_pos ha]
    exact (hex a ha).choose_spec.2
  · intro a ha b hb hab
    simp only [dif_pos ha, dif_pos hb] at hab
    have h1 : ‖a + s - (hex a ha).choose‖ ≤ r := (hex a ha).choose_spec.2
    have h2 : ‖b + s - (hex b hb).choose‖ ≤ r := (hex b hb).choose_spec.2
    rw [hab] at h1
    have h3 : ‖(a + s) - (b + s)‖ ≤ r := by
      have h2' : ‖(hex b hb).choose - (b + s)‖ ≤ r := by rw [norm_sub_rev]; exact h2
      exact norm_sub_le_of_le_of_le p h1 h2'
    rw [show (a + s) - (b + s) = a - b by ring] at h3
    exact hT.sep a ha b hb h3

variable (ψ : AddChar (p.adicCompletion ℚ) ℂ)

def avg (T : Finset F) : Module.End ℂ ↥(principalSeries2 p χ) :=
  ∑ a ∈ T, ψ (-a) • principalSeries2Rep χ (upperUnipotent2 p a)

theorem avg_apply (T : Finset F) (f : ↥(principalSeries2 p χ)) :
    avg p χ ψ T f = ∑ a ∈ T, ψ (-a) • principalSeries2Rep χ (upperUnipotent2 p a) f := by
  simp [avg, LinearMap.sum_apply, LinearMap.smul_apply]

theorem avg_generator_eq_zero {R r : ℝ} {T : Finset F} (hT : IsPart p R r T) (hrR : r ≤ R)
    (hψr : ∀ y : F, ‖y‖ ≤ r → ψ y = 1)
    {g : ↥(principalSeries2 p χ)} (hg : ∀ y : F, ‖y‖ ≤ r → principalSeries2Rep χ (upperUnipotent2 p y) g = g)
    {s : F} (hs : ‖s‖ ≤ R) :
    avg p χ ψ T (principalSeries2Rep χ (upperUnipotent2 p s) g - ψ s • g) = 0 := by
  classical
  obtain ⟨σ, hσT, hσclose, hσinj⟩ := exists_perm_of_isPart p hT hrR hs
  rw [map_sub, map_smul, avg_apply, avg_apply, sub_eq_zero]

  have hterm : ∀ a ∈ T, ψ (-a) • principalSeries2Rep χ (upperUnipotent2 p a)
      (principalSeries2Rep χ (upperUnipotent2 p s) g)
      = ψ s • (ψ (-σ a) • principalSeries2Rep χ (upperUnipotent2 p (σ a)) g) := by
    intro a ha
    set d : F := a + s - σ a with hd
    have hdr : ‖d‖ ≤ r := hσclose a ha
    have hns : upperUnipotent2 p a * upperUnipotent2 p s = upperUnipotent2 p (σ a) * upperUnipotent2 p d := by
      rw [upperUnipotent2_mul, upperUnipotent2_mul]
      congr 1
      rw [hd]
      ring
    rw [← rho_mul, hns, rho_mul, hg d hdr, smul_smul]
    congr 1
    have hψa : ψ (-a) = ψ s * ψ (-σ a) * ψ (-d) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      rw [hd]
      ring
    rw [hψa, hψr (-d) (by rwa [norm_neg]), mul_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum]
  congr 1

  refine Finset.sum_nbij σ hσT (fun a ha b hb hab => hσinj a ha b hb hab) ?_ (fun a _ => rfl)

  have hmaps : Set.MapsTo σ (T : Set F) (T : Set F) := fun a ha => hσT a ha
  have hinj : Set.InjOn σ (T : Set F) := fun a ha b hb hab => hσinj a ha b hb hab
  have hsurj : Set.SurjOn σ (T : Set F) (T : Set F) :=
    Finset.surjOn_of_injOn_of_card_le σ hmaps hinj le_rfl
  exact hsurj

def twistedDiff : Submodule ℂ ↥(principalSeries2 p χ) :=
  Submodule.span ℂ {d | ∃ (s : F) (g : ↥(principalSeries2 p χ)),
    d = principalSeries2Rep χ (upperUnipotent2 p s) g - ψ s • g}

def Killed (f : ↥(principalSeries2 p χ)) : Prop :=
  ∃ (R₀ r₀ : ℝ), 0 < r₀ ∧ ∀ (R r : ℝ) (T : Finset F), R₀ ≤ R → 0 < r → r ≤ r₀ → r ≤ R →
    IsPart p R r T → avg p χ ψ T f = 0

theorem killed_of_mem_twistedDiff (hψ : IsTame p ψ) {f : ↥(principalSeries2 p χ)}
    (hf : f ∈ twistedDiff p χ ψ) : Killed p χ ψ f := by
  obtain ⟨δ, hδ, hδtriv⟩ := hψ
  induction hf using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨s, g, rfl⟩ := hd
    obtain ⟨ε, hε, hεfix⟩ := exists_forall_rho_upper_eq p χ g
    refine ⟨‖s‖, min ε δ, lt_min hε hδ, fun R r T hR hr hrle hrR hT => ?_⟩
    exact avg_generator_eq_zero p χ ψ hT hrR (fun y hy => hδtriv y (le_trans hy (le_trans hrle (min_le_right _ _))))
      (fun y hy => hεfix y (le_trans hy (le_trans hrle (min_le_left _ _)))) hR
  | zero => exact ⟨0, 1, one_pos, fun R r T _ _ _ _ _ => map_zero _⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    obtain ⟨R₁, r₁, hr₁, hk₁⟩ := h₁
    obtain ⟨R₂, r₂, hr₂, hk₂⟩ := h₂
    refine ⟨max R₁ R₂, min r₁ r₂, lt_min hr₁ hr₂, fun R r T hR hr hrle hrR hT => ?_⟩
    rw [map_add, hk₁ R r T (le_trans (le_max_left _ _) hR) hr (le_trans hrle (min_le_left _ _)) hrR hT,
      hk₂ R r T (le_trans (le_max_right _ _) hR) hr (le_trans hrle (min_le_right _ _)) hrR hT, add_zero]
  | smul c f _ h =>
    obtain ⟨R₁, r₁, hr₁, hk₁⟩ := h
    refine ⟨R₁, r₁, hr₁, fun R r T hR hr hrle hrR hT => ?_⟩
    rw [map_smul, hk₁ R r T hR hr hrle hrR hT, smul_zero]

variable (U : Submodule ℂ ↥(principalSeries2 p χ))
  (hU : ∀ (x : p.adicCompletion ℚ), ∀ u ∈ U, principalSeries2Rep χ (upperUnipotent2 p x) u ∈ U)
  (ℓ : ↥U →ₗ[ℂ] ℂ)
  (hℓ : ∀ (x : p.adicCompletion ℚ) (u : ↥U),
    ℓ ⟨principalSeries2Rep χ (upperUnipotent2 p x) u, hU x u u.2⟩ = ψ x * ℓ u)

include hU hℓ

theorem apply_eq_zero_of_avg_eq_zero (u : ↥U) {T : Finset F} (hTne : T.Nonempty)
    (havg : avg p χ ψ T (u : ↥(principalSeries2 p χ)) = 0) : ℓ u = 0 := by
  classical

  set uT : ↥U := ∑ a ∈ T, ψ (-a) • (⟨principalSeries2Rep χ (upperUnipotent2 p a) u, hU a u u.2⟩ : ↥U) with huT
  have hcoe : ((uT : ↥U) : ↥(principalSeries2 p χ)) = avg p χ ψ T (u : ↥(principalSeries2 p χ)) := by
    rw [huT, avg_apply]
    simp
  have huT0 : uT = 0 := by
    apply Subtype.ext
    rw [hcoe, havg]
    rfl
  have hsum : ℓ uT = (T.card : ℂ) * ℓ u := by
    rw [huT, map_sum]
    have : ∀ a ∈ T, ℓ (ψ (-a) • (⟨principalSeries2Rep χ (upperUnipotent2 p a) u, hU a u u.2⟩ : ↥U)) = ℓ u := by
      intro a _
      rw [map_smul, hℓ a u, smul_eq_mul, ← mul_assoc, psi_neg_mul_self, one_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rw [huT0, map_zero] at hsum
  have hcard : (T.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hTne).ne'
  rcases mul_eq_zero.mp hsum.symm with h | h
  · exact absurd h hcard
  · exact h

theorem apply_eq_zero_of_mem_twistedDiff (u : ↥U)
    (hu : (u : ↥(principalSeries2 p χ)) ∈ twistedDiff p χ ψ) : ℓ u = 0 := by
  by_cases hψ : IsTame p ψ
  · obtain ⟨R₀, r₀, hr₀, hk⟩ := killed_of_mem_twistedDiff p χ ψ hψ hu
    set R : ℝ := max R₀ r₀ with hR
    obtain ⟨T, hT, hTne⟩ := exists_isPart p (le_trans (le_of_lt hr₀) (le_max_right _ _) : (0 : ℝ) ≤ R) hr₀
    exact apply_eq_zero_of_avg_eq_zero p χ ψ U hU ℓ hℓ u hTne
      (hk R r₀ T (le_max_left _ _) hr₀ le_rfl (le_max_right _ _) hT)
  ·
    obtain ⟨ε, hε, hεfix⟩ := exists_forall_rho_upper_eq p χ (u : ↥(principalSeries2 p χ))
    have hex : ∃ y : F, ‖y‖ ≤ ε ∧ ψ y ≠ 1 := by
      by_contra h
      push Not at h
      exact hψ ⟨ε, hε, h⟩
    obtain ⟨y, hyε, hy1⟩ := hex
    have h1 := hℓ y u
    have h2 : (⟨principalSeries2Rep χ (upperUnipotent2 p y) u, hU y u u.2⟩ : ↥U) = u :=
      Subtype.ext (hεfix y hyε)
    rw [h2] at h1
    have h3 : (ψ y - 1) * ℓ u = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hy1
    · exact h

theorem exists_extension :
    ∃ L : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ,
      (∀ (x : F) (f : ↥(principalSeries2 p χ)), L (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * L f) ∧
      ∀ u : ↥U, L (u : ↥(principalSeries2 p χ)) = ℓ u := by
  set K := twistedDiff p χ ψ with hK

  set fU : ↥(principalSeries2 p χ) →ₗ.[ℂ] ℂ := ⟨U, ℓ⟩ with hfU
  set gK : ↥(principalSeries2 p χ) →ₗ.[ℂ] ℂ := ⟨K, 0⟩ with hgK
  have hagree : ∀ (x : fU.domain) (y : gK.domain), (x : ↥(principalSeries2 p χ)) = y → fU x = gK y := by
    intro x y hxy
    show ℓ x = (0 : ↥K →ₗ[ℂ] ℂ) y
    rw [LinearMap.zero_apply]
    apply apply_eq_zero_of_mem_twistedDiff p χ ψ U hU ℓ hℓ x
    have : ((x : ↥U) : ↥(principalSeries2 p χ)) = (y : ↥(principalSeries2 p χ)) := hxy
    rw [this]
    exact y.2
  set S : ↥(principalSeries2 p χ) →ₗ.[ℂ] ℂ := fU.sup gK hagree with hS
  obtain ⟨Lext, hLext⟩ := LinearMap.exists_extend S.toFun
  have hLext_apply : ∀ (z : ↥(principalSeries2 p χ)) (hz : z ∈ S.domain), Lext z = S.toFun ⟨z, hz⟩ := by
    intro z hz
    have := congrArg (fun T : ↥S.domain →ₗ[ℂ] ℂ => T ⟨z, hz⟩) hLext
    simpa using this
  have hdom : S.domain = U ⊔ K := rfl

  have hLU : ∀ u : ↥U, Lext (u : ↥(principalSeries2 p χ)) = ℓ u := by
    intro u
    have hz : (u : ↥(principalSeries2 p χ)) ∈ S.domain := by
      rw [hdom]
      exact Submodule.mem_sup_left u.2
    rw [hLext_apply _ hz]
    have h := LinearPMap.sup_apply hagree u (0 : ↥gK.domain) ⟨(u : ↥(principalSeries2 p χ)), hz⟩
      (by simp)
    change (fU.sup gK hagree) ⟨(u : ↥(principalSeries2 p χ)), hz⟩ = ℓ u
    refine h.trans ?_
    show ℓ u + (0 : ↥K →ₗ[ℂ] ℂ) 0 = ℓ u
    rw [LinearMap.zero_apply, add_zero]
  have hLK : ∀ k : ↥(principalSeries2 p χ), k ∈ K → Lext k = 0 := by
    intro k hk
    have hz : k ∈ S.domain := by
      rw [hdom]
      exact Submodule.mem_sup_right hk
    rw [hLext_apply _ hz]
    have h := LinearPMap.sup_apply hagree (0 : ↥fU.domain) (⟨k, hk⟩ : ↥gK.domain) ⟨k, hz⟩ (by simp)
    change (fU.sup gK hagree) ⟨k, hz⟩ = 0
    refine h.trans ?_
    show ℓ 0 + (0 : ↥K →ₗ[ℂ] ℂ) ⟨k, hk⟩ = 0
    rw [map_zero, LinearMap.zero_apply, add_zero]
  refine ⟨Lext, fun x f => ?_, hLU⟩
  have hmem : principalSeries2Rep χ (upperUnipotent2 p x) f - ψ x • f ∈ K :=
    Submodule.subset_span ⟨x, f, rfl⟩
  have h0 := hLK _ hmem
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

end Main

end WhittakerPS2Ext
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.WhittakerPS2Ext"

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ)
    (U : Submodule ℂ ↥(principalSeries2 p χ))
    (hU : ∀ (x : p.adicCompletion ℚ), ∀ u ∈ U, principalSeries2Rep χ (upperUnipotent2 p x) u ∈ U)
    (ℓ : ↥U →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : p.adicCompletion ℚ) (u : ↥U),
      ℓ ⟨principalSeries2Rep χ (upperUnipotent2 p x) u, hU x u u.2⟩ = ψ x * ℓ u) :
    ∃ L : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ,
      (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p χ)),
        L (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * L f) ∧
      ∀ u : ↥U, L (u : ↥(principalSeries2 p χ)) = ℓ u :=
  WhittakerPS2Ext.exists_extension p χ ψ U hU ℓ hℓ

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.WhittakerPS2Ext"

end S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem (solution)
