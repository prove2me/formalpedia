-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.dualPartner_block_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3bacebe5-ca06-5260-816f-6f95991a3f96

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace RankinSelberg
namespace DualPartnerF5
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open scoped Matrix

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : G2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 p a b c d h : G2) : Mat) = !![a, b; c, d] := rfl

theorem unipotent_coe (x : F) : ((UnramifiedWhittaker.unipotent x : G2) : Mat) = !![1, x; 0, 1] := rfl

theorem gl_eq_of_entries {g h : G2}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G2) (i j : Fin 2) :
    ((g * h : G2) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_mul (x y : F) :
    (UnramifiedWhittaker.unipotent x : G2) * UnramifiedWhittaker.unipotent y = UnramifiedWhittaker.unipotent (x + y) := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe] <;> ring

theorem unipotent_zero : (UnramifiedWhittaker.unipotent (0 : F) : G2) = 1 := by
  apply gl_eq_of_entries <;> simp [unipotent_coe]

theorem unipotent_inv (x : F) : (UnramifiedWhittaker.unipotent x : G2)⁻¹ = UnramifiedWhittaker.unipotent (-x) := by
  apply inv_eq_of_mul_eq_one_right
  rw [unipotent_mul, add_neg_cancel, unipotent_zero]

theorem scalar2_coe (u : (F)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : Mat) = !![(u : F), 0; 0, (u : F)] := by
  show Matrix.scalar (Fin 2) (u : F) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]

theorem scalar_comm (z : (F)ˣ) (g : G2) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalar2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def tI : G2 →* G2 where
  toFun := AutomorphicForm.transposeInvN (Fin 2)
  map_one' := Units.ext (by rw [AutomorphicForm.coe_transposeInvN, inv_one, Units.val_one, Matrix.transpose_one])
  map_mul' := AutomorphicForm.transposeInvN_mul (Fin 2)

theorem tI_apply (g : G2) : tI p g = AutomorphicForm.transposeInvN (Fin 2) g := rfl

theorem tI_tI (g : G2) : tI p (tI p g) = g := AutomorphicForm.transposeInvN_transposeInvN (Fin 2) g

theorem continuous_tI : Continuous (tI p) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ (tI p)) = fun g : G2 => (((g⁻¹ : G2) : Mat))ᵀ := by
      funext g; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_transpose
  · have : (fun g : G2 => (((tI p g)⁻¹ : G2) : Mat)) = fun g : G2 => ((g : Mat))ᵀ := by
      funext g; rfl
    rw [this]
    exact Units.continuous_val.matrix_transpose

theorem coe_tI (g : G2) : ((tI p g : G2) : Mat) = (((g⁻¹ : G2) : Mat))ᵀ := rfl

theorem tI_unipotent (x : F) :
    tI p (UnramifiedWhittaker.unipotent x) = gl2 p 1 0 (-x) 1 (by simp) := by
  apply gl_eq_of_entries <;> rw [coe_tI, unipotent_inv, unipotent_coe] <;> simp [Matrix.transpose_apply]

theorem tI_scalar (z : (F)ˣ) :
    tI p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ := by
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ :=
    (map_inv _ z).symm
  apply gl_eq_of_entries <;> rw [coe_tI, hinv, scalar2_coe] <;> simp [Matrix.transpose_apply]

theorem d_mul_d (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) : d * d = 1 := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, hd]

theorem d_inv (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) : d⁻¹ = d :=
  inv_eq_of_mul_eq_one_right (d_mul_d p d hd)

theorem tI_d (d : G2) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1]) : tI p d = d := by
  apply gl_eq_of_entries <;> rw [coe_tI, d_inv p d hd, hd] <;> simp [Matrix.transpose_apply]

theorem w₀p_d_tI_unipotent (w₀p d : G2) (hw₀p : ((w₀p : G2) : Mat) = !![0, 1; 1, 0]) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1])
    (x : F) :
    w₀p * d * tI p (UnramifiedWhittaker.unipotent x) = UnramifiedWhittaker.unipotent x * (w₀p * d) := by
  rw [tI_unipotent]
  apply gl_eq_of_entries <;> simp [mul_coe_apply, hw₀p, hd, unipotent_coe]

theorem w₀p_tI_d_unipotent_mul (w₀p d : G2) (hw₀p : ((w₀p : G2) : Mat) = !![0, 1; 1, 0]) (hd : ((d : G2) : Mat) = !![1, 0; 0, -1])
    (x : F) (g : G2) :
    w₀p * tI p (d * (UnramifiedWhittaker.unipotent x * g)) = UnramifiedWhittaker.unipotent x * (w₀p * tI p (d * g)) := by
  rw [map_mul, map_mul, map_mul, tI_d p d hd, ← mul_assoc, ← mul_assoc, w₀p_d_tI_unipotent p w₀p d hw₀p hd,
    mul_assoc, mul_assoc]

def M (g : G2) : ℂ := ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ)

theorem M_eq_norm (g : G2) : M p g = ((‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ : ℝ) : ℂ) := by
  rw [M, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl

theorem M_mul (g h : G2) : M p (g * h) = M p g * M p h := by
  simp only [M_eq_norm, map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul]

theorem M_ne_zero (g : G2) : M p g ≠ 0 := by
  rw [M_eq_norm]; exact_mod_cast norm_ne_zero_iff.2 (Matrix.GeneralLinearGroup.det g).ne_zero

theorem M_unipotent (x : F) : M p (UnramifiedWhittaker.unipotent x) = 1 := by
  have : Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.unipotent x : G2) = 1 := by
    ext; rw [Matrix.GeneralLinearGroup.val_det_apply, unipotent_coe, Matrix.det_fin_two_of]; simp
  rw [M_eq_norm, this, Units.val_one, norm_one, Complex.ofReal_one]

theorem M_scalar (z : (F)ˣ) : M p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = (((‖(z : F)‖ ^ 2 : ℝ)) : ℂ) := by
  rw [M_eq_norm, Matrix.GeneralLinearGroup.val_det_apply, scalar2_coe, Matrix.det_fin_two_of]
  simp [sq]

abbrev kzero : Subgroup G2 := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

theorem isOpen_kzero : IsOpen (kzero p : Set G2) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2

theorem norm_le_one_of_mem {x : F} (hx : x ∈ p.adicCompletionIntegers ℚ) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 hx)

theorem norm_entry_le_one_of_mem_kzero {k : G2} (hk : k ∈ kzero p) (i j : Fin 2) : ‖(k : Mat) i j‖ ≤ 1 :=
  norm_le_one_of_mem p (((AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ p k).1 hk).1.integral i j)

theorem norm_det_le_one_of_entries {g : G2} (h : ∀ i j, ‖(g : Mat) i j‖ ≤ 1) :
    ‖((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)‖ ≤ 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (h 0 0) (norm_nonneg _) (h 1 1)
  · rw [norm_neg, norm_mul]; exact mul_le_one₀ (h 0 1) (norm_nonneg _) (h 1 0)

theorem M_of_mem_kzero {k : G2} (hk : k ∈ kzero p) : M p k = 1 := by
  have h1 : ‖((Matrix.GeneralLinearGroup.det k : (F)ˣ) : F)‖ ≤ 1 :=
    norm_det_le_one_of_entries p (norm_entry_le_one_of_mem_kzero p hk)
  have h2 : ‖((Matrix.GeneralLinearGroup.det k⁻¹ : (F)ˣ) : F)‖ ≤ 1 :=
    norm_det_le_one_of_entries p (norm_entry_le_one_of_mem_kzero p (inv_mem hk))
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((Matrix.GeneralLinearGroup.det k : (F)ˣ) : F)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have h3 : 1 ≤ ‖((Matrix.GeneralLinearGroup.det k : (F)ˣ) : F)‖ := by rwa [inv_le_one₀ hpos] at h2
  rw [M_eq_norm, le_antisymm h1 h3, Complex.ofReal_one]

section Span

variable {G : Type*} [Group G]

theorem comp_mul_mem_span (w : G → ℂ) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) (h : G) :
    (fun g => w' (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := by
  let R : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f g => f (g * h), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hR : R w' ∈ (Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))).map R :=
    Submodule.mem_map_of_mem hw'
  rw [Submodule.map_span] at hR
  refine (Submodule.span_mono ?_) hR
  rintro _ ⟨_, ⟨h', rfl⟩, rfl⟩
  exact ⟨h * h', by funext g; simp [R, mul_assoc]⟩

theorem law_of_mem_span (w : G → ℂ) (a : G) (c : ℂ) (hw : ∀ g : G, w (a * g) = c * w g) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∀ g : G, w' (a * g) = c * w' g := by
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro g
    show w (a * g * h) = c * w (g * h)
    rw [mul_assoc, hw]
  | zero => intro g; simp
  | add x y _ _ hx hy => intro g; simp only [Pi.add_apply, hx, hy, mul_add]
  | smul r x _ hx => intro g; simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

theorem smooth_of_mem_span [TopologicalSpace G] [ContinuousMul G] (w : G → ℂ)
    (hwsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w (g * k) = w g) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w' (g * k) = w' g := by
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨U, hUo, hU⟩ := hwsm
    refine ⟨U.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
      have : ((U.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (U : Set G) := by
        ext k; simp [Subgroup.coe_comap, MulAut.conj_apply]
      rw [this]
      exact hUo.preimage hc
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ U := by simpa [Subgroup.mem_comap, MulAut.conj_apply] using hk
      show w (g * k * h) = w (g * h)
      have := hU _ hk' (g * h)
      rw [← this]
      congr 1
      group
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h₁o, h₁⟩ := hx
    obtain ⟨U₂, h₂o, h₂⟩ := hy
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]; exact h₁o.inter h₂o
    · simp only [Pi.add_apply, h₁ k (Subgroup.mem_inf.1 hk).1 g, h₂ k (Subgroup.mem_inf.1 hk).2 g]
  | smul r x _ hx =>
    obtain ⟨U, ho, hU⟩ := hx
    exact ⟨U, ho, fun k hk g => by simp only [Pi.smul_apply, hU k hk g]⟩

theorem isLocallyConstant_of_open_stabilizer [TopologicalSpace G] [ContinuousMul G] {Y : Type*} (f : G → Y)
    (hsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, f (g * k) = f g) : IsLocallyConstant f := by
  obtain ⟨U, hU, h⟩ := hsm
  intro s
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, (Homeomorph.mulLeft g).isOpenMap _ hU, ⟨1, U.one_mem, mul_one g⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  show f (g * k) ∈ s
  rw [h k hk]; exact hg

end Span

def flat (w₀p d : G2) (f : G2 → ℂ) : G2 → ℂ :=
  fun g => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (F)ˣ) : F) : ℝ) : ℂ) * f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (d * g))

theorem flat_apply (w₀p d : G2) (f : G2 → ℂ) (g : G2) :
    flat p w₀p d f g = M p (d * g) * f (w₀p * tI p (d * g)) := rfl

def flatL (w₀p d : G2) : (G2 → ℂ) →ₗ[ℂ] (G2 → ℂ) where
  toFun := flat p w₀p d
  map_add' f₁ f₂ := by funext g; simp only [flat_apply, Pi.add_apply]; ring
  map_smul' c f := by funext g; simp only [flat_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem flatL_apply (w₀p d : G2) (f : G2 → ℂ) : flatL p w₀p d f = flat p w₀p d f := rfl

theorem flat_mul_right (w₀p d : G2) (f : G2 → ℂ) (g h : G2) :
    flat p w₀p d f (g * h) = M p h * flat p w₀p d (fun x => f (x * tI p h)) g := by
  simp only [flat_apply]
  rw [← mul_assoc d g h, M_mul, map_mul, ← mul_assoc w₀p]
  ring

theorem main
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) → w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1])
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) :
    let W : G2 → ℂ := flat p w₀p d w
    IsLocallyConstant W ∧
    (∀ (x : F) (g : G2), W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g) ∧
    (∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W (g * k) = W g) ∧
    (∀ U : Subgroup G2, IsOpen (U : Set G2) → ∃ B : Finset (G2 → ℂ),
      ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => W (g * h)),
        (∀ k ∈ U, ∀ g : G2, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G2 → ℂ))) ∧
    (∃ θ : (F)ˣ →* ℂˣ, ∀ (zc : (F)ˣ) (g : G2), W (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * W g) ∧
    (∀ g : G2, w (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * g) = ((θ₀ (-1) : ℂˣ) : ℂ) * w g) := by
  intro W

  have hwlaw : ∀ (x : F) (g : G2), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g :=
    fun x => law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hw
  have hwsm : ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, w (g * k) = w g :=
    smooth_of_mem_span w₂base ⟨AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N,
      (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2, hw₂K⟩ hw
  have hwcen : ∀ (z : (F)ˣ) (g : G2), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g :=
    fun z => law_of_mem_span w₂base _ _ (hcentral z) hw

  have h2 : ∀ (x : F) (g : G2), W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g := by
    intro x g
    show flat p w₀p d w _ = _ * flat p w₀p d w g
    simp only [flat_apply]
    rw [w₀p_tI_d_unipotent_mul p w₀p d hw₀p hd, hwlaw, ← mul_assoc d, M_mul, M_mul, M_mul, M_unipotent]
    ring

  have h3 : ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W (g * k) = W g := by
    obtain ⟨U, hUo, hU⟩ := hwsm
    refine ⟨U.comap (tI p) ⊓ kzero p, ?_, ?_⟩
    · rw [Subgroup.coe_inf, Subgroup.coe_comap]
      exact (hUo.preimage (continuous_tI p)).inter (isOpen_kzero p)
    · intro k hk g
      obtain ⟨hkU, hkK⟩ := Subgroup.mem_inf.1 hk
      rw [Subgroup.mem_comap] at hkU
      show flat p w₀p d w _ = flat p w₀p d w g
      rw [flat_mul_right, M_of_mem_kzero p hkK, one_mul, flat_apply, flat_apply, hU _ hkU]

  have h1 : IsLocallyConstant W := isLocallyConstant_of_open_stabilizer W h3

  have h4 : ∀ U : Subgroup G2, IsOpen (U : Set G2) → ∃ B : Finset (G2 → ℂ),
      ∀ w' ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => W (g * h)),
        (∀ k ∈ U, ∀ g : G2, w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (G2 → ℂ)) := by
    intro U hU

    set U₁ : Subgroup G2 := (U ⊓ kzero p).comap (tI p) with hU₁
    have hU₁o : IsOpen (U₁ : Set G2) := by
      rw [hU₁, Subgroup.coe_comap, Subgroup.coe_inf]
      exact (hU.inter (isOpen_kzero p)).preimage (continuous_tI p)
    obtain ⟨B, hB⟩ := hw₂adm U₁ hU₁o
    refine ⟨B.image (flatL p w₀p d), ?_⟩
    intro w' hw' hinv

    set V : Submodule ℂ (G2 → ℂ) := Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)) with hV
    have hle : Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => W (g * h)) ≤ V.map (flatL p w₀p d) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      have hmem : (fun x : G2 => w (x * tI p h)) ∈ V := comp_mul_mem_span w₂base hw (tI p h)
      have : (fun g : G2 => W (g * h)) = M p h • flatL p w₀p d (fun x : G2 => w (x * tI p h)) := by
        funext g
        show flat p w₀p d w (g * h) = _
        rw [flat_mul_right]; rfl
      beta_reduce
      rw [SetLike.mem_coe, this]
      exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hmem)
    obtain ⟨f, hfV, rfl⟩ := Submodule.mem_map.1 (hle hw')

    have hfinv : ∀ k₁ ∈ U₁, ∀ h : G2, f (h * k₁) = f h := by
      intro k₁ hk₁ h
      have hk : tI p k₁ ∈ U ⊓ kzero p := by rw [hU₁, Subgroup.mem_comap] at hk₁; exact hk₁
      obtain ⟨hkU, hkK⟩ := Subgroup.mem_inf.1 hk
      set g : G2 := d⁻¹ * tI p (w₀p⁻¹ * h) with hg
      have hg' : w₀p * tI p (d * g) = h := by
        rw [hg, ← mul_assoc, mul_inv_cancel, one_mul, tI_tI, ← mul_assoc, mul_inv_cancel, one_mul]
      have := hinv (tI p k₁) hkU g
      rw [flatL_apply, flat_mul_right, M_of_mem_kzero p hkK, one_mul, flat_apply, flat_apply, hg', tI_tI] at this
      exact mul_left_cancel₀ (M_ne_zero p _) this
    have hfB : f ∈ Submodule.span ℂ (B : Set (G2 → ℂ)) := hB f hfV hfinv
    rw [Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hfB

  have h5 : ∃ θ : (F)ˣ →* ℂˣ, ∀ (zc : (F)ˣ) (g : G2),
      W (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * W g := by
    have hne : ∀ z : (F)ˣ, (((‖(z : F)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := fun z => by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 z.ne_zero)
    let θf : (F)ˣ → ℂˣ := fun z => Units.mk0 _ (hne z) * (θ₀ z)⁻¹
    have hθf : ∀ a b : (F)ˣ, θf (a * b) = θf a * θf b := by
      intro a b
      apply Units.ext
      simp only [θf, Units.val_mul, Units.val_mk0, map_mul, mul_inv, Units.val_inv_eq_inv_val, norm_mul, mul_pow,
        Complex.ofReal_mul]
      ring
    refine ⟨MonoidHom.mk' θf hθf, fun zc g => ?_⟩
    show flat p w₀p d w _ = _ * flat p w₀p d w g
    simp only [MonoidHom.mk'_apply, θf, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, flat_apply]
    have e1 : d * (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = Matrix.GeneralLinearGroup.scalar (Fin 2) zc * (d * g) := by
      rw [← mul_assoc, scalar_comm p zc d, mul_assoc]
    have e2 : ∀ X : G2, w₀p * (Matrix.GeneralLinearGroup.scalar (Fin 2) zc⁻¹ * X) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) zc⁻¹ * (w₀p * X) := fun X => by
      rw [← mul_assoc, scalar_comm p zc⁻¹ w₀p, mul_assoc]
    rw [e1, M_mul, M_scalar, map_mul, tI_scalar, e2, hwcen, map_inv, Units.val_inv_eq_inv_val]
    ring

  have h6 : ∀ g : G2, w (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * g) = ((θ₀ (-1) : ℂˣ) : ℂ) * w g := hwcen (-1)
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end LanglandsTunnell.RankinSelberg.DualPartnerF5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell.RankinSelberg.DualPartnerF5"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell.RankinSelberg"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible.LanglandsTunnell.RankinSelberg.DualPartnerF5"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) → w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1])
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) :

    IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) ∧

    (∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) g) ∧

    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (g * k) = (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) g) ∧

    (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) → w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧

    (∃ θ : (p.adicCompletion ℚ)ˣ →* ℂˣ, ∀ (zc : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * g) = ((θ zc : ℂˣ) : ℂ) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) (d * g))) g) ∧

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * g) = ((θ₀ (-1) : ℂˣ) : ℂ) * w g) :=
  LanglandsTunnell.RankinSelberg.DualPartnerF5.main p θ₀ N hN w₂base hw₂law hw₂K hw₂adm hcentral w₀p hw₀p d hd w hw

end S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_dualPartner_block_of_admissible (solution)
