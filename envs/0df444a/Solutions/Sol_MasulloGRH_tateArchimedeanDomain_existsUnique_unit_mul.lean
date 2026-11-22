-- Prove2me | solution 1 for MasulloGRH.tateArchimedeanDomain_existsUnique_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:40:25.852063+00:00
-- url     : https://prove2.me/submissions/cab20080-2336-44ef-8244-8a820ce5a8ff

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tateArchimedeanDomain_existsUnique_unit_mul

open MasulloGRH RiemannMasullo NumberField.Units.dirichletUnitTheorem InfinitePlace.Completion
open scoped Classical

variable (F : Type*) [Field F] [NumberField F]

/-! ### The diagonal embedding of the units -/

omit [NumberField F] in
theorem unitsToInfiniteIdeles_val (u : (𝓞 F)ˣ) (v : InfinitePlace F) :
    (unitsToInfiniteIdeles F u).val v = (((u : 𝓞 F) : F) : v.Completion) := rfl

omit [NumberField F] in
theorem norm_unitsToInfiniteIdeles (u : (𝓞 F)ˣ) (v : InfinitePlace F) :
    ‖(unitsToInfiniteIdeles F u).val v‖ = v ((u : 𝓞 F) : F) := by
  rw [unitsToInfiniteIdeles_val]
  exact InfinitePlace.Completion.norm_coe v _

/-- A diagonal global unit has archimedean norm one (product formula for units). -/
theorem unitsToInfiniteIdeles_mem_ker (u : (𝓞 F)ˣ) :
    unitsToInfiniteIdeles F u ∈ MonoidHom.ker (infiniteIdeleNorm F) := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  apply NNReal.coe_injective
  simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val, NNReal.coe_prod,
    NNReal.coe_pow, Units.val_one, NNReal.coe_one]
  change ∏ v : InfinitePlace F, (‖(unitsToInfiniteIdeles F u).val v‖₊ : ℝ) ^ v.mult = 1
  simp_rw [coe_nnnorm, norm_unitsToInfiniteIdeles, InfinitePlace.prod_eq_abs_norm, Units.norm]
  norm_cast

/-! ### The logarithm map in the coordinates of the trace-zero hyperplane -/

/-- The logarithm map, in Mathlib's coordinates `logSpace F` (the place `w₀` is dropped). -/
noncomputable def L (g : (InfiniteAdeleRing F)ˣ) : logSpace F :=
  fun w ↦ infiniteIdeleLog F g w.val

theorem L_mul (g h : (InfiniteAdeleRing F)ˣ) : L F (g * h) = L F g + L F h := by
  have hne (u : (InfiniteAdeleRing F)ˣ) (v : InfinitePlace F) : u.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v).toMonoidHom u).ne_zero
  funext w
  change (w.val.mult : ℝ) * Real.log ‖(g.val * h.val) w.val‖ =
    w.val.mult * Real.log ‖g.val w.val‖ + w.val.mult * Real.log ‖h.val w.val‖
  rw [← mul_add, ← Real.log_mul (norm_ne_zero_iff.mpr (hne g _)) (norm_ne_zero_iff.mpr (hne h _)),
    ← norm_mul]
  rfl

theorem L_unit (u : (𝓞 F)ˣ) :
    L F (unitsToInfiniteIdeles F u) = Units.logEmbedding F (Additive.ofMul u) := by
  funext w
  rw [logEmbedding_component]
  change (w.val.mult : ℝ) * Real.log ‖(unitsToInfiniteIdeles F u).val w.val‖ = _
  rw [norm_unitsToInfiniteIdeles]

variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

/-- The integer span of the basis of the parallelotope is the image of the logarithmic
embedding of the units. -/
theorem mem_span_iff (y : logSpace F) :
    y ∈ Submodule.span ℤ (Set.range
      ((b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F))) ↔
      ∃ u : (𝓞 F)ˣ, Units.logEmbedding F (Additive.ofMul u) = y := by
  rw [Module.Basis.ofZLatticeBasis_span, Units.unitLattice, Submodule.map_top]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toMul, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Additive.ofMul u, rfl⟩

/-- Covering: every point of the hyperplane is moved into the parallelotope by the logarithm of
a unit. -/
theorem exists_unit_log_add_mem (y : logSpace F) :
    ∃ u : (𝓞 F)ˣ, Units.logEmbedding F (Additive.ofMul u) + y ∈ regulatorParallelotope F b := by
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)) y
  obtain ⟨u, hu⟩ := (mem_span_iff F b v.val).mp v.prop
  exact ⟨u, by rw [hu]; exact hv⟩

/-- Disjointness: a unit whose logarithm translates one point of the parallelotope to another one
has logarithm zero. -/
theorem log_eq_zero_of_add_mem (u : (𝓞 F)ˣ) (y : logSpace F)
    (hy : y ∈ regulatorParallelotope F b)
    (h : Units.logEmbedding F (Additive.ofMul u) + y ∈ regulatorParallelotope F b) :
    Units.logEmbedding F (Additive.ofMul u) = 0 := by
  obtain ⟨v, -, hv⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)) y
  have h₁ := hv ⟨_, (mem_span_iff F b _).mpr ⟨u, rfl⟩⟩ h
  have h₀ := hv 0 (by
    change (0 : Submodule.span ℤ (Set.range
      ((b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)))) +ᵥ y ∈
        regulatorParallelotope F b
    rw [zero_vadd]
    exact hy)
  exact congrArg Subtype.val (h₁.trans h₀.symm)

/-! ### The coordinate at `v₀` -/

variable (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)

/-- The coordinate at `v₀`, read in `ℂ` through `σ ∘ extensionEmbedding v₀`. -/
noncomputable def coord : (InfiniteAdeleRing F)ˣ →* ℂˣ :=
  (Units.map (σ.toRingHom.comp (extensionEmbedding v₀)).toMonoidHom).comp
    (Units.map (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v₀).toMonoidHom)

/-- The complex embedding `σ ∘ v₀.embedding` of `F`. -/
noncomputable def φ : F →+* ℂ := σ.toRingHom.comp v₀.embedding

omit [NumberField F] in
theorem coord_unit (u : (𝓞 F)ˣ) :
    coord F v₀ σ (unitsToInfiniteIdeles F u) = Units.complexEmbedding (φ F v₀ σ) u := by
  apply Units.ext
  change σ (extensionEmbedding v₀ ((unitsToInfiniteIdeles F u).val v₀)) =
    σ (v₀.embedding ((u : 𝓞 F) : F))
  rw [unitsToInfiniteIdeles_val]
  congr 1
  exact extensionEmbedding_coe v₀ _

/-! ### The sector at `v₀` is a strict fundamental domain for the roots of unity -/

/-- Some root of unity of `F` rotates the coordinate at `v₀` into the sector `[0, 2π / w_F)`. -/
theorem exists_torsion_mul_mem_sector (g : (InfiniteAdeleRing F)ˣ) :
    ∃ ζ ∈ Units.torsion F,
      ((coord F v₀ σ (unitsToInfiniteIdeles F ζ * g) : ℂˣ) : ℂ).arg ∈
        Set.Ico 0 (2 * Real.pi / Units.torsionOrder F) := by
  have hn0 : Units.torsionOrder F ≠ 0 := Units.torsionOrder_ne_zero F
  have hn : 0 < (Units.torsionOrder F : ℝ) := by exact_mod_cast Units.torsionOrder_pos F
  have hn₂ : (2 : ℝ) ≤ Units.torsionOrder F := by
    obtain ⟨m, hm⟩ := Units.even_torsionOrder F
    have := Units.torsionOrder_pos F
    exact_mod_cast (by omega : 2 ≤ Units.torsionOrder F)
  have hp : 0 < 2 * Real.pi / Units.torsionOrder F := div_pos Real.two_pi_pos hn
  have hpπ : 2 * Real.pi / Units.torsionOrder F ≤ Real.pi :=
    (div_le_iff₀ hn).mpr (by nlinarith [Real.pi_pos])
  obtain ⟨k, hk, -⟩ := existsUnique_add_zsmul_mem_Ico hp
    ((coord F v₀ σ g : ℂˣ) : ℂ).arg 0
  rw [zero_add] at hk
  have hw : Complex.exp (((2 * Real.pi / Units.torsionOrder F : ℝ) : ℂ) * Complex.I) ^
      Units.torsionOrder F = 1 := by
    have h := (Complex.isPrimitiveRoot_exp (Units.torsionOrder F) hn0).pow_eq_one
    rw [← h]
    congr 2
    push_cast
    ring
  have hζ : Units.mk0 (Complex.exp (((2 * Real.pi / Units.torsionOrder F : ℝ) : ℂ) * Complex.I))
      (Complex.exp_ne_zero _) ∈ rootsOfUnity (Units.torsionOrder F) ℂ :=
    (mem_rootsOfUnity' _ _).mpr hw
  rw [← Units.map_complexEmbedding_torsion F (φ F v₀ σ)] at hζ
  obtain ⟨u, hu, hmap⟩ := hζ
  have hmap' : Units.complexEmbedding (φ F v₀ σ) u = Units.mk0 _ (Complex.exp_ne_zero _) := hmap
  refine ⟨u ^ k, zpow_mem hu k, ?_⟩
  rw [map_mul, map_zpow, map_zpow, coord_unit, hmap', Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_mk0]
  have hrotate : Complex.exp (((2 * Real.pi / Units.torsionOrder F : ℝ) : ℂ) * Complex.I) ^ k *
      ((coord F v₀ σ g : ℂˣ) : ℂ) =
      ((‖((coord F v₀ σ g : ℂˣ) : ℂ)‖ : ℝ) : ℂ) *
        Complex.exp (((((coord F v₀ σ g : ℂˣ) : ℂ).arg +
          k • (2 * Real.pi / Units.torsionOrder F) : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ((coord F v₀ σ g : ℂˣ) : ℂ)]
    rw [← Complex.exp_int_mul, zsmul_eq_mul, mul_left_comm (Complex.exp _), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrotate, Complex.arg_real_mul _ (norm_pos_iff.mpr (coord F v₀ σ g).ne_zero),
    Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).mpr]
  · exact hk
  · refine ⟨(neg_lt_zero.mpr Real.pi_pos).trans_le hk.1, ?_⟩
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact hk.2.le.trans hpπ

/-- A root of unity of `F` that maps one point of the sector at `v₀` to another one is `1`. -/
theorem torsion_eq_one_of_sector (w : (𝓞 F)ˣ) (hw : w ∈ Units.torsion F)
    (g h : (InfiniteAdeleRing F)ˣ) (hmul : unitsToInfiniteIdeles F w * g = h)
    (hg : ((coord F v₀ σ g : ℂˣ) : ℂ).arg ∈ Set.Ico 0 (2 * Real.pi / Units.torsionOrder F))
    (hh : ((coord F v₀ σ h : ℂˣ) : ℂ).arg ∈ Set.Ico 0 (2 * Real.pi / Units.torsionOrder F)) :
    w = 1 := by
  have hn0 : Units.torsionOrder F ≠ 0 := Units.torsionOrder_ne_zero F
  have hn : 0 < (Units.torsionOrder F : ℝ) := by exact_mod_cast Units.torsionOrder_pos F
  have hzmem : Units.complexEmbedding (φ F v₀ σ) w ∈ rootsOfUnity (Units.torsionOrder F) ℂ := by
    rw [← Units.map_complexEmbedding_torsion F (φ F v₀ σ)]
    exact Subgroup.mem_map_of_mem _ hw
  have hz : ((Units.complexEmbedding (φ F v₀ σ) w : ℂˣ) : ℂ) ^ Units.torsionOrder F = 1 :=
    (mem_rootsOfUnity' _ _).mp hzmem
  have hcoord : ((Units.complexEmbedding (φ F v₀ σ) w : ℂˣ) : ℂ) * ((coord F v₀ σ g : ℂˣ) : ℂ) =
      ((coord F v₀ σ h : ℂˣ) : ℂ) := by
    rw [← hmul, map_mul, coord_unit, Units.val_mul]
  have hpow : ((coord F v₀ σ g : ℂˣ) : ℂ) ^ Units.torsionOrder F =
      ((coord F v₀ σ h : ℂˣ) : ℂ) ^ Units.torsionOrder F := by
    rw [← hcoord, mul_pow, hz, one_mul]
  have hang : (((Units.torsionOrder F : ℝ) * ((coord F v₀ σ g : ℂˣ) : ℂ).arg : ℝ) : Real.Angle) =
      (((Units.torsionOrder F : ℝ) * ((coord F v₀ σ h : ℂˣ) : ℂ).arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.natCast_mul_eq_nsmul, Real.Angle.natCast_mul_eq_nsmul,
      ← Complex.arg_pow_coe_angle, ← Complex.arg_pow_coe_angle, hpow]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have h1 : ((coord F v₀ σ g : ℂˣ) : ℂ).arg * Units.torsionOrder F < 2 * Real.pi :=
    (lt_div_iff₀ hn).mp hg.2
  have h2 : ((coord F v₀ σ h : ℂˣ) : ℂ).arg * Units.torsionOrder F < 2 * Real.pi :=
    (lt_div_iff₀ hn).mp hh.2
  have h3 : 0 ≤ ((coord F v₀ σ g : ℂˣ) : ℂ).arg * Units.torsionOrder F := mul_nonneg hg.1 hn.le
  have h4 : 0 ≤ ((coord F v₀ σ h : ℂˣ) : ℂ).arg * Units.torsionOrder F := mul_nonneg hh.1 hn.le
  have hk0 : k = 0 := by
    have hlt : (-1 : ℝ) < k ∧ (k : ℝ) < 1 := by
      constructor <;> nlinarith [Real.pi_pos]
    have hlt' : -1 < k ∧ k < 1 := by exact_mod_cast hlt
    omega
  have hargs : ((coord F v₀ σ g : ℂˣ) : ℂ).arg = ((coord F v₀ σ h : ℂˣ) : ℂ).arg := by
    rw [hk0, Int.cast_zero, mul_zero] at hk
    exact mul_left_cancel₀ hn.ne' (sub_eq_zero.mp hk)
  have hznorm : ‖((Units.complexEmbedding (φ F v₀ σ) w : ℂˣ) : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hz hn0
  have hac : ((coord F v₀ σ g : ℂˣ) : ℂ) = ((coord F v₀ σ h : ℂˣ) : ℂ) :=
    Complex.ext_norm_arg (by rw [← hcoord, norm_mul, hznorm, one_mul]) hargs
  have hz1 : ((Units.complexEmbedding (φ F v₀ σ) w : ℂˣ) : ℂ) = 1 :=
    mul_right_cancel₀ (coord F v₀ σ g).ne_zero (by rw [hcoord, one_mul, hac])
  have hone : Units.complexEmbedding (φ F v₀ σ) w = Units.complexEmbedding (φ F v₀ σ) 1 := by
    rw [map_one]
    exact Units.ext hz1
  exact Units.complexEmbedding_injective (φ F v₀ σ) hone

/-! ### Existence and uniqueness -/

theorem mem_domain_iff (e : MonoidHom.ker (infiniteIdeleNorm F)) :
    e ∈ tateArchimedeanDomain F b v₀ σ ↔
      L F e.val ∈ regulatorParallelotope F b ∧
        ((coord F v₀ σ e.val : ℂˣ) : ℂ).arg ∈ Set.Ico 0 (2 * Real.pi / Units.torsionOrder F) :=
  Iff.rfl

/-- Covering: `𝒪_Fˣ E₀ = 𝕀_∞¹`. -/
theorem exists_unit (g : MonoidHom.ker (infiniteIdeleNorm F)) :
    ∃ u : (𝓞 F)ˣ, ∃ e ∈ tateArchimedeanDomain F b v₀ σ,
      (g : (InfiniteAdeleRing F)ˣ) =
        unitsToInfiniteIdeles F u * (e : (InfiniteAdeleRing F)ˣ) := by
  obtain ⟨u₁, hu₁⟩ := exists_unit_log_add_mem F b (L F g.val)
  obtain ⟨ζ, hζ, hsector⟩ :=
    exists_torsion_mul_mem_sector F v₀ σ (unitsToInfiniteIdeles F u₁ * g.val)
  have hmem : unitsToInfiniteIdeles F ζ * (unitsToInfiniteIdeles F u₁ * g.val) ∈
      MonoidHom.ker (infiniteIdeleNorm F) :=
    mul_mem (unitsToInfiniteIdeles_mem_ker F ζ)
      (mul_mem (unitsToInfiniteIdeles_mem_ker F u₁) g.prop)
  refine ⟨(ζ * u₁)⁻¹, ⟨_, hmem⟩, (mem_domain_iff F b v₀ σ _).mpr ⟨?_, hsector⟩, ?_⟩
  · change L F (unitsToInfiniteIdeles F ζ * (unitsToInfiniteIdeles F u₁ * g.val)) ∈ _
    rw [L_mul, L_mul, L_unit, L_unit, logEmbedding_eq_zero_iff.mpr hζ, zero_add]
    exact hu₁
  · change g.val = unitsToInfiniteIdeles F (ζ * u₁)⁻¹ *
      (unitsToInfiniteIdeles F ζ * (unitsToInfiniteIdeles F u₁ * g.val))
    rw [map_inv, map_mul, ← mul_assoc (unitsToInfiniteIdeles F ζ), inv_mul_cancel_left]

/-- Disjointness of the translates: the unit `u` in `g = u e`, `e ∈ E₀`, is determined by `g`. -/
theorem unit_unique (u u' : (𝓞 F)ˣ) (e e' : MonoidHom.ker (infiniteIdeleNorm F))
    (he : e ∈ tateArchimedeanDomain F b v₀ σ) (he' : e' ∈ tateArchimedeanDomain F b v₀ σ)
    (h : unitsToInfiniteIdeles F u * e.val = unitsToInfiniteIdeles F u' * e'.val) : u' = u := by
  rw [mem_domain_iff] at he he'
  have hmul : unitsToInfiniteIdeles F (u⁻¹ * u') * e'.val = e.val := by
    rw [map_mul, map_inv, mul_assoc, ← h, inv_mul_cancel_left]
  have hL : Units.logEmbedding F (Additive.ofMul (u⁻¹ * u')) + L F e'.val = L F e.val := by
    rw [← L_unit, ← L_mul, hmul]
  have hzero : Units.logEmbedding F (Additive.ofMul (u⁻¹ * u')) = 0 :=
    log_eq_zero_of_add_mem F b (u⁻¹ * u') (L F e'.val) he'.1 (hL ▸ he.1)
  have htors : u⁻¹ * u' ∈ Units.torsion F := logEmbedding_eq_zero_iff.mp hzero
  have hone : u⁻¹ * u' = 1 :=
    torsion_eq_one_of_sector F v₀ σ (u⁻¹ * u') htors e'.val e.val hmul he'.2 he.2
  exact (inv_mul_eq_one.mp hone).symm

end Sol_MasulloGRH_tateArchimedeanDomain_existsUnique_unit_mul

open MasulloGRH Sol_MasulloGRH_tateArchimedeanDomain_existsUnique_unit_mul in
theorem solution
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (g : MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F)) :
    ∃! u : (𝓞 F)ˣ, ∃ e ∈ tateArchimedeanDomain F b v₀ σ,
      (g : (InfiniteAdeleRing F)ˣ) =
        unitsToInfiniteIdeles F u * (e : (InfiniteAdeleRing F)ˣ) := by
  obtain ⟨u, e, he, hg⟩ := exists_unit F b v₀ σ g
  refine ⟨u, ⟨e, he, hg⟩, ?_⟩
  rintro u' ⟨e', he', hg'⟩
  exact unit_unique F b v₀ σ u u' e e' he he' (hg.symm.trans hg')
