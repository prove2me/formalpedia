-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_linearMap_principalSeries2_of_jacquet_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/32a53cfb-32a8-59b7-a9d3-a88f987916b9

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top

set_option autoImplicit false

noncomputable section

namespace JacquetPS2

section SchurDixmier

open Polynomial

variable {Q : Type} [AddCommGroup Q] [Module ℂ Q]

theorem aeval_injective_of_forall_sub_smul_injective (τ : Module.End ℂ Q)
    (hτ : ∀ c : ℂ, Function.Injective ⇑(τ - c • (1 : Module.End ℂ Q))) :
    ∀ P : ℂ[X], P ≠ 0 → Function.Injective ⇑(aeval τ P) := by
  intro P
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    by_cases hdeg : P.degree = 0
    · rw [eq_C_of_degree_eq_zero hdeg]
      have ha : P.coeff 0 ≠ 0 := by
        intro h
        have := eq_C_of_degree_eq_zero hdeg
        rw [h, map_zero] at this
        exact hP this
      intro x y hxy
      simp only [aeval_C, Module.algebraMap_end_apply] at hxy
      exact smul_right_injective Q ha hxy
    · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hdeg
      have hmul : (X - C r) * (P /ₘ (X - C r)) = P := mul_divByMonic_eq_iff_isRoot.mpr hr
      have hP' : P /ₘ (X - C r) ≠ 0 := by
        intro h
        rw [h, mul_zero] at hmul
        exact hP hmul.symm
      have hpos : 0 < P.natDegree := by
        rw [natDegree_pos_iff_degree_pos]
        rcases lt_trichotomy P.degree 0 with h | h | h
        · exact absurd (degree_eq_bot.mp (by
            rcases Nat.WithBot.lt_zero_iff.mp h with h'
            exact h')) hP
        · exact absurd h hdeg
        · exact h
      have hlt : (P /ₘ (X - C r)).natDegree < n := by
        have := natDegree_divByMonic P (monic_X_sub_C r)
        rw [natDegree_X_sub_C] at this
        omega
      have hinj' := ih _ hlt (P /ₘ (X - C r)) rfl hP'
      rw [← hmul, map_mul]
      have hlin : aeval τ (X - C r) = τ - r • (1 : Module.End ℂ Q) := by
        rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      rw [hlin, Module.End.mul_eq_comp, LinearMap.coe_comp]
      exact (hτ r).comp hinj'

theorem exists_forall_apply_eq_smul_of_stable
    (S : Set Q) (hSc : S.Countable) (hSspan : Submodule.span ℂ S = ⊤)
    (𝒯 : Set (Module.End ℂ Q)) (τ : Module.End ℂ Q)
    (hcomm : ∀ σ ∈ 𝒯, σ * τ = τ * σ)
    (hsimple : ∀ W : Submodule ℂ Q, (∀ σ ∈ 𝒯, ∀ q ∈ W, σ q ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ c : ℂ, ∀ q, τ q = c • q := by
  by_cases htriv : ∀ q : Q, q = 0
  · exact ⟨0, fun q => by rw [htriv (τ q), htriv q, smul_zero]⟩
  push Not at htriv
  obtain ⟨q₀, hq₀⟩ := htriv
  by_contra hno
  push Not at hno
  have hcomm' : ∀ σ ∈ 𝒯, ∀ (c : ℂ) (q : Q),
      (τ - c • (1 : Module.End ℂ Q)) (σ q) = σ ((τ - c • (1 : Module.End ℂ Q)) q) := by
    intro σ hσ c q
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    rw [← Module.End.mul_apply, ← hcomm σ hσ, Module.End.mul_apply]
  have hinj : ∀ c : ℂ, Function.Injective ⇑(τ - c • (1 : Module.End ℂ Q)) := by
    intro c
    rcases hsimple (LinearMap.ker (τ - c • 1)) (fun σ hσ q hq => by
        rw [LinearMap.mem_ker] at hq ⊢
        rw [hcomm' σ hσ, hq, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exfalso
      obtain ⟨q, hq⟩ := hno c
      have hmem : q ∈ LinearMap.ker (τ - c • 1) := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at hmem
      exact hq hmem
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(τ - c • (1 : Module.End ℂ Q)) := by
    intro c
    rcases hsimple (LinearMap.range (τ - c • 1)) (fun σ hσ q hq => by
        obtain ⟨q', rfl⟩ := LinearMap.mem_range.mp hq
        exact LinearMap.mem_range.mpr ⟨σ q', hcomm' σ hσ c q'⟩) with h | h
    · exfalso
      have hmem : (τ - c • 1) q₀ ∈ LinearMap.range (τ - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at hmem
      exact hq₀ (hinj c (by rw [hmem, map_zero]))
    · exact LinearMap.range_eq_top.mp h

  let R : ℂ → (Q ≃ₗ[ℂ] Q) := fun c => LinearEquiv.ofBijective (τ - c • 1) ⟨hinj c, hsurj c⟩
  let f : ℂ → Q := fun c => (R c).symm q₀
  have hf : ∀ c, (τ - c • (1 : Module.End ℂ Q)) (f c) = q₀ := fun c => (R c).apply_symm_apply q₀
  have hfX : ∀ c, aeval τ (X - C c) (f c) = q₀ := by
    intro c
    rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    exact hf c
  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro s g hsum i hi

    set L : ℂ[X] := ∑ j ∈ s, g j • ∏ k ∈ s.erase j, (X - C k) with hL
    have hLq : aeval τ L q₀ = 0 := by
      have hterm : ∀ j ∈ s, aeval τ (∏ k ∈ s.erase j, (X - C k)) q₀
          = aeval τ (∏ k ∈ s, (X - C k)) (f j) := by
        intro j hj
        conv_lhs => rw [← hfX j]
        rw [← Module.End.mul_apply, ← map_mul, Finset.prod_erase_mul _ _ hj]
      rw [hL, map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply]
      rw [Finset.sum_congr rfl fun j hj => by rw [hterm j hj]]
      simp only [← map_smul]
      rw [← map_sum, hsum, map_zero]
    have hL0 : L = 0 := by
      by_contra hne
      exact hq₀ (aeval_injective_of_forall_sub_smul_injective τ hinj L hne (by rw [hLq, map_zero]))

    have heval := congrArg (Polynomial.eval i) hL0
    rw [hL, eval_zero, eval_finsetSum, Finset.sum_eq_single i] at heval
    · rw [eval_smul, eval_prod, smul_eq_mul, mul_eq_zero] at heval
      rcases heval with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨k, hk, hk0⟩ := h
        rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk0
        exact (Finset.ne_of_mem_erase hk) hk0.symm
    · intro j hj hji
      rw [eval_smul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji, hi⟩)
        (by rw [eval_sub, eval_X, eval_C, sub_self]), smul_zero]
    · intro h
      exact absurd hi h
  have h1 : Cardinal.mk ℂ ≤ Module.rank ℂ Q := hli.cardinal_le_rank
  have h2 : Module.rank ℂ Q ≤ Cardinal.aleph0 := by
    rw [← rank_top, ← hSspan]
    exact (rank_span_le S).trans hSc.le_aleph0
  have h3 := h1.trans h2
  rw [Cardinal.mk_complex] at h3
  exact Cardinal.aleph0_lt_continuum.not_ge h3

end SchurDixmier

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Matrix TopologicalSpace

section Group

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

scoped instance secondCountable_matrix : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))

scoped instance secondCountable_matrix_op : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.isInducing.secondCountableTopology

scoped instance secondCountable_gl : SecondCountableTopology G :=
  Units.isInducing_embedProduct.secondCountableTopology

theorem countable_range_of_isLocallyConstant {Y : Type*} (f : G → Y) (hf : IsLocallyConstant f) :
    (Set.range f).Countable := by
  have h := Set.PairwiseDisjoint.countable_of_isOpen (s := fun y : Y => f ⁻¹' {y}) (a := Set.range f)
    (fun y _ y' _ hne => Set.disjoint_iff.mpr fun x ⟨hx, hx'⟩ => hne (hx.symm.trans hx'))
    (fun y _ => hf.isOpen_fiber y)
    (fun y hy => by obtain ⟨x, rfl⟩ := hy; exact ⟨x, rfl⟩)
  exact h

theorem isInducing_units_val : Topology.IsInducing (Units.val : Fˣ → F) :=
  Units.isEmbedding_val₀.isInducing

theorem exists_higherUnitsAt_subset {U : Set Fˣ} (hU : IsOpen U) (h1 : (1 : Fˣ) ∈ U) :
    ∃ n : ℕ, ∀ u ∈ higherUnitsAt ℚ p n, u ∈ U := by
  obtain ⟨O, hO, hOU⟩ := (isInducing_units_val p).isOpen_iff.mp hU
  have hmem : O ∈ nhds ((1 : Fˣ) : F) := hO.mem_nhds (by
    have : (1 : Fˣ) ∈ Units.val ⁻¹' O := hOU ▸ h1
    exact this)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hmem
  set γ' : WithZero (Multiplicative ℤ) :=
    MonoidWithZeroHom.ValueGroup₀.embedding γ.val with hγ'def
  have hγ0 : γ' ≠ 0 := (map_ne_zero _).mpr γ.ne_zero
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero hγ0) with hm
  have hγm : γ' = WithZero.exp m := by
    rw [hm]
    simp [WithZero.exp]
  refine ⟨(-m).toNat + 1, fun u hu => ?_⟩
  rw [mem_higherUnitsAt_iff] at hu
  obtain ⟨-, hu⟩ := hu
  rcases hu with h | h
  · omega
  · rw [← hOU, Set.mem_preimage]
    apply hγ
    show Valued.v.restrict ((u : F) - ((1 : Fˣ) : F)) < γ.val
    rw [Valuation.restrict_lt_iff_lt_embedding, Units.val_one]
    refine lt_of_le_of_lt h ?_
    show WithZero.exp (-(((-m).toNat + 1 : ℕ) : ℤ)) < γ'
    rw [hγm, WithZero.exp_lt_exp]
    have := Int.self_le_toNat (-m)
    push_cast
    omega

theorem norm_eq_one_of_valued_eq_one {u : F} (h : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, h, map_one, NNReal.coe_one]

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

theorem continuous_diagonal2 : Continuous (diagonal2 p) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun a : Fin 2 → Fˣ => Matrix.diagonal fun i => (a i : F)
    exact Continuous.matrix_diagonal (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i))
  · show Continuous fun a : Fin 2 → Fˣ => Matrix.diagonal fun i => (((a i)⁻¹ : Fˣ) : F)
    exact Continuous.matrix_diagonal
      (continuous_pi fun i => Units.continuous_coe_inv.comp (continuous_apply i))

theorem unipotent_eq (x : F) : (UnramifiedWhittaker.unipotent x : G) = upperUnipotent2 p x := by
  ext i j
  rfl

@[scoped simp] theorem diagonal2_one : diagonal2 p 1 = 1 := by
  ext i j
  simp [diagonal2, Matrix.one_apply]

theorem diagonal2_coe' (a : Fin 2 → Fˣ) :
    ((diagonal2 p a : G) : Matrix (Fin 2) (Fin 2) F) = !![(a 0 : F), 0; 0, (a 1 : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagonal2_mul_upperUnipotent2 (a : Fin 2 → Fˣ) (t : F) :
    diagonal2 p a * upperUnipotent2 p t
      = upperUnipotent2 p ((a 0 : F) * t * (((a 1)⁻¹ : Fˣ) : F)) * diagonal2 p a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

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

set_option linter.unnecessarySeqFocus false in

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
  ·
    have hD0 : D ≠ 0 := by
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
  ·
    push Not at hcd
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

local notation "ρ" => rightTranslate2 p

theorem rho_apply (h : G) (f : G → ℂ) : ρ h f = fun g => f (g * h) := rfl

theorem rho_rho (h h' : G) (f : G → ℂ) : ρ h (ρ h' f) = ρ (h * h') f := by
  rw [rightTranslate2_mul]
  rfl

@[scoped simp] theorem rho_one (f : G → ℂ) : ρ 1 f = f := by
  funext g
  simp [rightTranslate2_apply]

def cyc (w : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))

theorem rho_mem_cyc_self (w : G → ℂ) (h : G) : ρ h w ∈ cyc p w :=
  Submodule.subset_span ⟨h, rfl⟩

theorem self_mem_cyc (w : G → ℂ) : w ∈ cyc p w := by
  simpa using rho_mem_cyc_self p w 1

theorem rho_mem_cyc {w f : G → ℂ} (hf : f ∈ cyc p w) (h : G) : ρ h f ∈ cyc p w := by
  have hle : Submodule.map (ρ h) (cyc p w) ≤ cyc p w := by
    rw [cyc, Submodule.map_span_le]
    rintro _ ⟨h', rfl⟩
    show ρ h (ρ h' w) ∈ cyc p w
    rw [rho_rho]
    exact rho_mem_cyc_self p w _
  exact hle ⟨f, hf, rfl⟩

theorem cyc_le_of_mem {w w' : G → ℂ} (h : w' ∈ cyc p w) : cyc p w' ≤ cyc p w := by
  rw [cyc, Submodule.span_le]
  rintro _ ⟨h', rfl⟩
  exact rho_mem_cyc p h h'

def diff (w : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {D : G → ℂ | ∃ W' ∈ cyc p w, ∃ t : F,
    D = fun g : G => W' (g * UnramifiedWhittaker.unipotent t) - W' g}

theorem sub_mem_diff {w W' : G → ℂ} (hW' : W' ∈ cyc p w) (t : F) :
    ρ (upperUnipotent2 p t) W' - W' ∈ diff p w := by
  refine Submodule.subset_span ⟨W', hW', t, ?_⟩
  funext g
  rw [← unipotent_eq]
  rfl

theorem diff_le_cyc (w : G → ℂ) : diff p w ≤ cyc p w := by
  rw [diff, Submodule.span_le]
  rintro _ ⟨W', hW', t, rfl⟩
  have : (fun g : G => W' (g * UnramifiedWhittaker.unipotent t) - W' g)
      = ρ (UnramifiedWhittaker.unipotent t) W' - W' := rfl
  rw [this]
  exact (cyc p w).sub_mem (rho_mem_cyc p hW' _) hW'

theorem rho_diagonal2_mem_diff {w d : G → ℂ} (hd : d ∈ diff p w) (a : Fin 2 → Fˣ) :
    ρ (diagonal2 p a) d ∈ diff p w := by
  have hle : Submodule.map (ρ (diagonal2 p a)) (diff p w) ≤ diff p w := by
    rw [diff, Submodule.map_span_le]
    rintro _ ⟨W', hW', t, rfl⟩
    have : (fun g : G => W' (g * UnramifiedWhittaker.unipotent t) - W' g)
        = ρ (upperUnipotent2 p t) W' - W' := by
      rw [unipotent_eq]; rfl
    rw [this, map_sub, rho_rho, diagonal2_mul_upperUnipotent2, ← rho_rho]
    exact sub_mem_diff p (rho_mem_cyc p hW' _) _
  exact hle ⟨d, hd, rfl⟩

def IsSmooth (f : G → ℂ) : Prop :=
  ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ∀ u ∈ U, ∀ g : G, f (g * u) = f g

theorem IsSmooth.zero : IsSmooth p (0 : G → ℂ) := ⟨Set.univ, isOpen_univ, trivial, fun _ _ _ => rfl⟩

theorem IsSmooth.add {f₁ f₂ : G → ℂ} (h₁ : IsSmooth p f₁) (h₂ : IsSmooth p f₂) : IsSmooth p (f₁ + f₂) := by
  obtain ⟨U₁, hU₁, h1₁, hf₁⟩ := h₁
  obtain ⟨U₂, hU₂, h1₂, hf₂⟩ := h₂
  exact ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨h1₁, h1₂⟩, fun u hu g => by
    simp only [Pi.add_apply, hf₁ u hu.1, hf₂ u hu.2]⟩

theorem IsSmooth.smul {f : G → ℂ} (c : ℂ) (h : IsSmooth p f) : IsSmooth p (c • f) := by
  obtain ⟨U, hU, h1, hf⟩ := h
  exact ⟨U, hU, h1, fun u hu g => by simp only [Pi.smul_apply, hf u hu]⟩

theorem IsSmooth.rho {f : G → ℂ} (h : IsSmooth p f) (x : G) : IsSmooth p (ρ x f) := by
  obtain ⟨U, hU, h1, hf⟩ := h
  refine ⟨(fun u => x⁻¹ * u * x) ⁻¹' U, hU.preimage (by fun_prop), by simpa using h1, fun u hu g => ?_⟩
  simp only [rightTranslate2_apply]
  have : g * u * x = g * x * (x⁻¹ * u * x) := by group
  rw [this, hf _ hu]

def smoothVectors : Submodule ℂ (G → ℂ) where
  carrier := {f | IsSmooth p f}
  zero_mem' := IsSmooth.zero p
  add_mem' := IsSmooth.add p
  smul_mem' := fun c _ hf => IsSmooth.smul p c hf

theorem cyc_le_smoothVectors {w : G → ℂ} (hw : IsSmooth p w) : cyc p w ≤ smoothVectors p := by
  rw [cyc, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  exact hw.rho p h

end Group

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "ρ" => rightTranslate2 p

variable (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₀ : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N,
    ∀ g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), w₀ (g * k) = w₀ g)

def subV (M : Submodule ℂ (G → ℂ)) : Submodule ℂ ↥(cyc p w₀) := M.comap (cyc p w₀).subtype

def rhoV (a : Fin 2 → Fˣ) : ↥(cyc p w₀) →ₗ[ℂ] ↥(cyc p w₀) :=
  (ρ (diagonal2 p a)).restrict fun _ hv => rho_mem_cyc p hv _

theorem rhoV_coe (a : Fin 2 → Fˣ) (v : ↥(cyc p w₀)) : (rhoV p w₀ a v : G → ℂ) = ρ (diagonal2 p a) v := rfl

def tau (M : Submodule ℂ (G → ℂ)) (hMT : ∀ a : Fin 2 → Fˣ, ∀ m ∈ M, ρ (diagonal2 p a) m ∈ M)
    (a : Fin 2 → Fˣ) : Module.End ℂ (↥(cyc p w₀) ⧸ subV p w₀ M) :=
  (subV p w₀ M).mapQ (subV p w₀ M) (rhoV p w₀ a) fun _ hv => hMT a _ hv

theorem tau_mkQ (M : Submodule ℂ (G → ℂ)) (hMT : ∀ a : Fin 2 → Fˣ, ∀ m ∈ M, ρ (diagonal2 p a) m ∈ M)
    (a : Fin 2 → Fˣ) (v : ↥(cyc p w₀)) :
    tau p w₀ M hMT a ((subV p w₀ M).mkQ v) = (subV p w₀ M).mkQ (rhoV p w₀ a v) :=
  Submodule.mapQ_apply _ _ _ _

theorem tau_comm (M : Submodule ℂ (G → ℂ)) (hMT : ∀ a : Fin 2 → Fˣ, ∀ m ∈ M, ρ (diagonal2 p a) m ∈ M)
    (a b : Fin 2 → Fˣ) : tau p w₀ M hMT a * tau p w₀ M hMT b = tau p w₀ M hMT b * tau p w₀ M hMT a := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := (subV p w₀ M).mkQ_surjective q
  rw [Module.End.mul_apply, Module.End.mul_apply, tau_mkQ, tau_mkQ, tau_mkQ, tau_mkQ]
  congr 1
  apply Subtype.ext
  rw [rhoV_coe, rhoV_coe, rhoV_coe, rhoV_coe, rho_rho, rho_rho, ← diagonal2_mul, ← diagonal2_mul, mul_comm]

def toQ (M : Submodule ℂ (G → ℂ)) (f : G → ℂ) : ↥(cyc p w₀) ⧸ subV p w₀ M := by
  classical
  exact if hf : f ∈ cyc p w₀ then (subV p w₀ M).mkQ ⟨f, hf⟩ else 0

theorem toQ_of_mem (M : Submodule ℂ (G → ℂ)) {f : G → ℂ} (hf : f ∈ cyc p w₀) :
    toQ p w₀ M f = (subV p w₀ M).mkQ ⟨f, hf⟩ := by
  classical
  exact dif_pos hf

theorem span_range_toQ (M : Submodule ℂ (G → ℂ)) :
    Submodule.span ℂ (Set.range (toQ p w₀ M ∘ fun h : G => ρ h w₀)) = ⊤ := by
  have key : ∀ (f : G → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₀ (g * h))),
      (subV p w₀ M).mkQ ⟨f, hf⟩ ∈ Submodule.span ℂ (Set.range (toQ p w₀ M ∘ fun h : G => ρ h w₀)) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨h, rfl⟩ := hf
      refine Submodule.subset_span ⟨h, ?_⟩
      show toQ p w₀ M (ρ h w₀) = _
      rw [toQ_of_mem]
      rfl
    | zero =>
      have : (⟨0, Submodule.zero_mem _⟩ : ↥(cyc p w₀)) = 0 := rfl
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | add f g hf hg ihf ihg =>
      have : (⟨f + g, Submodule.add_mem _ hf hg⟩ : ↥(cyc p w₀)) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
      rw [this, map_add]
      exact Submodule.add_mem _ ihf ihg
    | smul c f hf ihf =>
      have : (⟨c • f, Submodule.smul_mem _ c hf⟩ : ↥(cyc p w₀)) = c • ⟨f, hf⟩ := rfl
      rw [this, map_smul]
      exact Submodule.smul_mem _ c ihf
  rw [eq_top_iff]
  rintro q -
  obtain ⟨⟨v, hv⟩, rfl⟩ := (subV p w₀ M).mkQ_surjective q
  exact key v hv

include hN hK in

theorem isSmooth_gen : IsSmooth p w₀ :=
  ⟨(AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set G), (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2,
    SetLike.mem_coe.mpr (one_mem _), fun k hk g => hK k hk g⟩

include hN hK in

theorem isLocallyConstant_rho_gen : IsLocallyConstant fun h : G => ρ h w₀ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro k
  refine ⟨(fun x => k⁻¹ * x) ⁻¹' (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set G),
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2.preimage (continuous_const_mul _),
    ?_, fun x hx => ?_⟩
  · show k⁻¹ * k ∈ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set G)
    rw [inv_mul_cancel]
    exact SetLike.mem_coe.mpr (one_mem _)
  · have hx' : k⁻¹ * x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := hx
    have h1 : ρ (k⁻¹ * x) w₀ = w₀ := funext fun g => hK _ hx' g
    calc ρ x w₀ = ρ (k * (k⁻¹ * x)) w₀ := by rw [mul_inv_cancel_left]
      _ = ρ k (ρ (k⁻¹ * x) w₀) := (rho_rho p _ _ _).symm
      _ = ρ k w₀ := by rw [h1]

include hN hK in

theorem countable_range_toQ_rho (M : Submodule ℂ (G → ℂ)) :
    (Set.range (toQ p w₀ M ∘ fun h : G => ρ h w₀)).Countable :=
  countable_range_of_isLocallyConstant p _ ((isLocallyConstant_rho_gen p N hN w₀ hK).comp _)

include hN hK in

theorem finite_image_iwasawaSet : ((fun k : G => ρ k w₀) '' iwasawaSet p).Finite := by
  haveI : CompactSpace ↥(iwasawaSet p) := isCompact_iff_compactSpace.mp (isCompact_iwasawaSet p)
  have h := ((isLocallyConstant_rho_gen p N hN w₀ hK).comp_continuous
    (continuous_subtype_val : Continuous ((↑) : ↥(iwasawaSet p) → G))).range_finite
  rwa [Set.range_comp, Subtype.range_coe] at h

theorem cyc_le_diff_sup_span :
    cyc p w₀ ≤ diff p w₀ ⊔ Submodule.span ℂ
      {f | ∃ a : Fin 2 → Fˣ, ∃ s ∈ (fun k : G => ρ k w₀) '' iwasawaSet p, f = ρ (diagonal2 p a) s} := by
  rw [cyc, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  obtain ⟨x, a, k, hk, hh⟩ := iwasawa' p h
  have h1 : (fun g : G => w₀ (g * h)) = ρ (upperUnipotent2 p x) (ρ (diagonal2 p a) (ρ k w₀)) := by
    rw [rho_rho, rho_rho, ← hh]; rfl
  suffices hsuff : (fun g : G => w₀ (g * h)) ∈ diff p w₀ ⊔ Submodule.span ℂ
      {f | ∃ a : Fin 2 → Fˣ, ∃ s ∈ (fun k : G => ρ k w₀) '' iwasawaSet p, f = ρ (diagonal2 p a) s} from hsuff
  rw [h1]
  have hvV : ρ (diagonal2 p a) (ρ k w₀) ∈ cyc p w₀ := rho_mem_cyc p (rho_mem_cyc_self p w₀ k) _
  have : ρ (upperUnipotent2 p x) (ρ (diagonal2 p a) (ρ k w₀))
      = (ρ (upperUnipotent2 p x) (ρ (diagonal2 p a) (ρ k w₀)) - ρ (diagonal2 p a) (ρ k w₀))
        + ρ (diagonal2 p a) (ρ k w₀) := by abel
  rw [this]
  exact Submodule.add_mem_sup (sub_mem_diff p hvV x) (Submodule.subset_span ⟨a, ρ k w₀, ⟨k, hk, rfl⟩, rfl⟩)

def torusStable : Set (Submodule ℂ (G → ℂ)) :=
  {M | diff p w₀ ≤ M ∧ M ≤ cyc p w₀ ∧ ¬ cyc p w₀ ≤ M ∧ ∀ a : Fin 2 → Fˣ, ∀ m ∈ M, ρ (diagonal2 p a) m ∈ M}

theorem diff_mem_torusStable (hJ : ¬ cyc p w₀ ≤ diff p w₀) : diff p w₀ ∈ torusStable p w₀ :=
  ⟨le_rfl, diff_le_cyc p w₀, hJ, fun a _ hm => rho_diagonal2_mem_diff p hm a⟩

include hN hK in

theorem exists_maximal_torusStable (hJ : ¬ cyc p w₀ ≤ diff p w₀) :
    ∃ M, Maximal (· ∈ torusStable p w₀) M := by
  have hchain : ∀ c ⊆ torusStable p w₀, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ torusStable p w₀, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hchain.directedOn
    refine ⟨sSup c, ⟨?_, ?_, ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · exact (hc hy).1.trans (le_sSup hy)
    · exact sSup_le fun M hM => (hc hM).2.1
    · intro hle

      obtain ⟨S, hS⟩ := (finite_image_iwasawaSet p N hN w₀ hK).exists_finset_coe
      have hSc : ∀ s ∈ S, ∃ M ∈ c, (s : G → ℂ) ∈ M := by
        intro s hs
        have hs' : (s : G → ℂ) ∈ (fun k : G => ρ k w₀) '' iwasawaSet p := by
          rw [← hS]; exact hs
        obtain ⟨k, -, hk⟩ := hs'
        rw [← hk]
        exact (Submodule.mem_sSup_of_directed hne hdir).mp (hle (rho_mem_cyc_self p w₀ k))
      choose! Mof hMc hMs using hSc

      haveI : Nonempty c := hne.to_subtype
      have hdir' : Directed (· ≤ ·) (fun M : c => (M : Submodule ℂ (G → ℂ))) := hdir.directed_val
      obtain ⟨Mz, hMz⟩ := hdir'.finset_le
        (S.attach.image fun s : {x // x ∈ S} => (⟨Mof s.1, hMc s.1 s.2⟩ : c))
      have hSM : ∀ s ∈ S, (s : G → ℂ) ∈ (Mz : Submodule ℂ (G → ℂ)) := by
        intro s hs
        have := hMz ⟨Mof s, hMc s hs⟩
          (Finset.mem_image.mpr ⟨(⟨s, hs⟩ : {x // x ∈ S}), Finset.mem_attach _ _, rfl⟩)
        exact this (hMs s hs)
      have hMzT := hc Mz.2
      apply hMzT.2.2.1
      refine (cyc_le_diff_sup_span p w₀).trans (sup_le hMzT.1 ?_)
      rw [Submodule.span_le]
      rintro _ ⟨a, s, hs, rfl⟩
      have hs' : s ∈ (S : Set (G → ℂ)) := by rw [hS]; exact hs
      exact hMzT.2.2.2 a s (hSM s hs')
    · intro a m hm
      obtain ⟨M, hMc, hmM⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hm
      exact (Submodule.mem_sSup_of_directed hne hdir).mpr ⟨M, hMc, (hc hMc).2.2.2 a m hmM⟩
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ (torusStable p w₀) hchain (diff p w₀) (diff_mem_torusStable p w₀ hJ)
  exact ⟨M, hM⟩

include hN hK in

theorem exists_eigenfunctional (hJ : ¬ cyc p w₀ ≤ diff p w₀) :
    ∃ (lam : (G → ℂ) →ₗ[ℂ] ℂ) (ω : (Fin 2 → Fˣ) → ℂ) (v₁ : G → ℂ), v₁ ∈ cyc p w₀ ∧ lam v₁ = 1 ∧
      (∀ d ∈ diff p w₀, lam d = 0) ∧
      ∀ v ∈ cyc p w₀, ∀ a : Fin 2 → Fˣ, lam (ρ (diagonal2 p a) v) = ω a * lam v := by
  obtain ⟨M, hM⟩ := exists_maximal_torusStable p N hN w₀ hK hJ
  obtain ⟨hDM, hMV, hVM, hMT⟩ := hM.prop

  have hsimple : ∀ W : Submodule ℂ (↥(cyc p w₀) ⧸ subV p w₀ M),
      (∀ σ ∈ Set.range (tau p w₀ M hMT), ∀ q ∈ W, σ q ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let Wt : Submodule ℂ (G → ℂ) := (W.comap (subV p w₀ M).mkQ).map (cyc p w₀).subtype
    have hMWt : M ≤ Wt := by
      intro m hm
      refine ⟨⟨m, hMV hm⟩, ?_, rfl⟩
      show (subV p w₀ M).mkQ ⟨m, hMV hm⟩ ∈ W
      have h0 : (subV p w₀ M).mkQ ⟨m, hMV hm⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero (subV p w₀ M)).mpr (show (⟨m, hMV hm⟩ : ↥(cyc p w₀)) ∈ subV p w₀ M from hm)
      rw [h0]
      exact W.zero_mem
    have hWtV : Wt ≤ cyc p w₀ := by
      rintro _ ⟨v, -, rfl⟩
      exact v.2
    have hWtT : ∀ a : Fin 2 → Fˣ, ∀ m ∈ Wt, ρ (diagonal2 p a) m ∈ Wt := by
      rintro a _ ⟨v, hv, rfl⟩
      refine ⟨rhoV p w₀ a v, ?_, rfl⟩
      show (subV p w₀ M).mkQ (rhoV p w₀ a v) ∈ W
      rw [← tau_mkQ p w₀ M hMT]
      exact hW _ ⟨a, rfl⟩ _ hv
    by_cases hVWt : cyc p w₀ ≤ Wt
    · right
      rw [eq_top_iff]
      rintro q -
      obtain ⟨v, rfl⟩ := (subV p w₀ M).mkQ_surjective q
      obtain ⟨v', hv', hv'v⟩ := hVWt v.2
      have : v' = v := Subtype.ext hv'v
      rw [← this]
      exact hv'
    · left
      have hWt : Wt ∈ torusStable p w₀ := ⟨hDM.trans hMWt, hWtV, hVWt, hWtT⟩
      have hle : Wt ≤ M := hM.le_of_ge hWt hMWt
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨v, rfl⟩ := (subV p w₀ M).mkQ_surjective q
      have hvWt : (v : G → ℂ) ∈ Wt := ⟨v, hq, rfl⟩
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hle hvWt

  have hscalar : ∀ a, ∃ c : ℂ, ∀ q, tau p w₀ M hMT a q = c • q := fun a =>
    exists_forall_apply_eq_smul_of_stable _ (countable_range_toQ_rho p N hN w₀ hK M) (span_range_toQ p w₀ M)
      (Set.range (tau p w₀ M hMT)) (tau p w₀ M hMT a)
      (by rintro _ ⟨b, rfl⟩; exact tau_comm p w₀ M hMT b a) hsimple
  choose ω hω using hscalar

  obtain ⟨v₁, hv₁V, hv₁M⟩ := SetLike.not_le_iff_exists.mp hVM
  obtain ⟨lam, hlamM, hlam1⟩ := LinearMap.exists_extend_of_notMem (0 : ↥M →ₗ[ℂ] ℂ) hv₁M (1 : ℂ)
  have hlam0 : ∀ m ∈ M, lam m = 0 := fun m hm => by
    have := LinearMap.congr_fun hlamM ⟨m, hm⟩
    simpa using this
  refine ⟨lam, ω, v₁, hv₁V, hlam1, fun d hd => hlam0 d (hDM hd), fun v hv a => ?_⟩

  have hmem : ρ (diagonal2 p a) v - ω a • v ∈ M := by
    have h := hω a ((subV p w₀ M).mkQ ⟨v, hv⟩)
    rw [tau_mkQ, ← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact h
  have := hlam0 _ hmem
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
  exact this

include hN hK in

theorem main (hirr : ∀ w ∈ cyc p w₀, w ≠ 0 → w₀ ∈ cyc p w) (hJ : ∃ W ∈ cyc p w₀, W ∉ diff p w₀) :
    ∃ (χ : Fin 2 → (Fˣ →* ℂˣ)) (c : Fin 2 → ℕ) (Φ : (G → ℂ) →ₗ[ℂ] (G → ℂ)),
      (∀ i, ∀ u ∈ higherUnitsAt ℚ p (c i), χ i u = 1) ∧
      (∀ w ∈ cyc p w₀, ∀ h : G, Φ (fun g => w (g * h)) = fun g => Φ w (g * h)) ∧
      (∀ w ∈ cyc p w₀, Φ w = 0 → w = 0) ∧
      (∀ w ∈ cyc p w₀, Φ w ∈ principalSeries2 p χ) := by
  have hJ' : ¬ cyc p w₀ ≤ diff p w₀ := fun hle => by
    obtain ⟨W, hW, hWD⟩ := hJ
    exact hWD (hle hW)
  obtain ⟨lam, ω, v₁, hv₁, hlam1, hlamD, hlamT⟩ := exists_eigenfunctional p N hN w₀ hK hJ'

  have hω_mul : ∀ a b, ω (a * b) = ω a * ω b := by
    intro a b
    have h := hlamT v₁ hv₁ (a * b)
    rw [diagonal2_mul, ← rho_rho, hlamT _ (rho_mem_cyc p hv₁ _) a, hlamT v₁ hv₁ b, hlam1, mul_one,
      mul_one] at h
    exact h.symm
  have hω_one : ω 1 = 1 := by
    have h := hlamT v₁ hv₁ 1
    rw [diagonal2_one, rho_one, hlam1, mul_one] at h
    exact h.symm
  have hω_ne : ∀ a, ω a ≠ 0 := fun a h0 => by
    have := hω_mul a a⁻¹
    rw [mul_inv_cancel, hω_one, h0, zero_mul] at this
    exact one_ne_zero this

  let η : (Fin 2 → Fˣ) →* ℂ :=
    { toFun := fun a => ω a * (halfModulus2 p a)⁻¹
      map_one' := by simp [hω_one]
      map_mul' := fun a b => by
        rw [hω_mul, halfModulus2_mul, mul_inv]
        ring }
  have hη : ∀ a, η a = ω a * (halfModulus2 p a)⁻¹ := fun a => rfl
  let χ : Fin 2 → (Fˣ →* ℂˣ) := fun i => η.toHomUnits.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Fˣ) i)
  have hχ : ∀ i (u : Fˣ), ((χ i u : ℂˣ) : ℂ) = η (Pi.mulSingle i u) := fun i u => rfl
  have htorus : ∀ a, torusChar2 p χ a * halfModulus2 p a = ω a := by
    intro a
    have h1 : torusChar2 p χ a = η a := by
      show (∏ i : Fin 2, ((χ i (a i) : ℂˣ) : ℂ)) = η a
      rw [Finset.prod_congr rfl fun i _ => hχ i (a i), ← map_prod, Finset.univ_prod_mulSingle]
    rw [h1, hη, inv_mul_cancel_right₀ (halfModulus2_ne_zero p a)]

  obtain ⟨U, hU, h1U, hUv⟩ := cyc_le_smoothVectors p (isSmooth_gen p N hN w₀ hK) hv₁
  have hωU : ∀ a, diagonal2 p a ∈ U → ω a = 1 := by
    intro a ha
    have h := hlamT v₁ hv₁ a
    have hfix : ρ (diagonal2 p a) v₁ = v₁ := funext fun g => hUv _ ha g
    rw [hfix, hlam1, mul_one] at h
    exact h.symm
  have hopen : ∀ i : Fin 2, IsOpen {u : Fˣ | diagonal2 p (Pi.mulSingle i u) ∈ U} := fun i =>
    hU.preimage ((continuous_diagonal2 p).comp (continuous_mulSingle i))
  have hone : ∀ i : Fin 2, (1 : Fˣ) ∈ {u : Fˣ | diagonal2 p (Pi.mulSingle i u) ∈ U} := fun i => by
    show diagonal2 p (Pi.mulSingle i 1) ∈ U
    rw [Pi.mulSingle_one, diagonal2_one]
    exact h1U
  choose c hc using fun i => exists_higherUnitsAt_subset p (hopen i) (hone i)

  let Φ : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f g => lam (ρ g f)
      map_add' := fun f₁ f₂ => by
        funext g
        simp only [map_add, Pi.add_apply]
      map_smul' := fun r f => by
        funext g
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul] }
  have hΦ : ∀ (f : G → ℂ) (g : G), Φ f g = lam (ρ g f) := fun f g => rfl

  have hequiv : ∀ (w : G → ℂ) (h : G), Φ (ρ h w) = fun g => Φ w (g * h) := by
    intro w h
    funext g
    rw [hΦ, hΦ, rho_rho]

  have hvan : ∀ w : G → ℂ, Φ w = 0 → ∀ f ∈ cyc p w, Φ f = 0 := by
    intro w hw
    have hle : cyc p w ≤ LinearMap.ker Φ := by
      rw [cyc, Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      show Φ (ρ h w) = 0
      rw [hequiv, hw]
      rfl
    exact fun f hf => hle hf
  refine ⟨χ, c, Φ, ?_, ?_, ?_, ?_⟩
  ·
    intro i u hu
    apply Units.ext
    rw [hχ, hη, hωU _ (hc i u hu), one_mul, Units.val_one]
    have hnorm : ‖(u : F)‖ = 1 := norm_eq_one_of_valued_eq_one p ((mem_higherUnitsAt_iff ℚ p).mp hu).1
    have : halfModulus2 p (Pi.mulSingle i u) = 1 := by
      fin_cases i <;> simp [halfModulus2, hnorm]
    rw [this, inv_one]
  ·
    intro w _ h
    exact hequiv w h
  ·
    intro w hw hΦw
    by_contra hw0
    have h0 : Φ v₁ = 0 := hvan w₀ (hvan w hΦw w₀ (hirr w hw hw0)) v₁ hv₁
    have : Φ v₁ 1 = 1 := by rw [hΦ, rho_one, hlam1]
    rw [h0] at this
    exact zero_ne_one this
  ·
    intro w hw
    refine mem_principalSeries2_iff.mpr ⟨?_, ?_, ?_⟩
    ·
      obtain ⟨U', hU', h1', hU'w⟩ := cyc_le_smoothVectors p (isSmooth_gen p N hN w₀ hK) hw
      rw [IsLocallyConstant.iff_exists_open]
      intro g
      refine ⟨(fun x => g⁻¹ * x) ⁻¹' U', hU'.preimage (continuous_const_mul _), ?_, fun x hx => ?_⟩
      · show g⁻¹ * g ∈ U'
        rwa [inv_mul_cancel]
      · have hx' : g⁻¹ * x ∈ U' := hx
        have hfix : ρ (g⁻¹ * x) w = w := funext fun g' => hU'w _ hx' g'
        rw [hΦ, hΦ]
        conv_lhs => rw [← mul_inv_cancel_left g x, ← rho_rho, hfix]
    ·
      intro x g
      rw [hΦ, hΦ, ← rho_rho]
      have hmem : ρ (upperUnipotent2 p x) (ρ g w) - ρ g w ∈ diff p w₀ := sub_mem_diff p (rho_mem_cyc p hw g) x
      have := hlamD _ hmem
      rw [map_sub, sub_eq_zero] at this
      exact this
    ·
      intro a g
      rw [hΦ, hΦ, ← rho_rho, hlamT _ (rho_mem_cyc p hw g) a, htorus]

end Main

end JacquetPS2
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top.JacquetPS2"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hJ : ∃ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      W ∉ Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g}) :
    ∃ (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (c : Fin 2 → ℕ)
      (Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)),
      (∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), χ i u = 1) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        Φ (fun g => w (g * h)) = fun g => Φ w (g * h)) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w = 0 → w = 0) ∧
      (∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φ w ∈ principalSeries2 p χ) :=
  JacquetPS2.main p N _hN w₂base hw₂K hw₂irr hJ

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top.JacquetPS2"

end S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_principalSeries2_of_jacquet_ne_top (solution)
