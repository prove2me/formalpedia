-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e2316b52-dc3a-5a17-b1e9-7fffda6b5104

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact.NumberField.AdelicFourier IsDedekindDomain"
open scoped SchwartzMap Topology ContDiff
open Filter

noncomputable section

namespace SchwartzMajorantCore

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable (V) in

def bumpData : ContDiffBump (0 : V) := ⟨2, 3, by norm_num, by norm_num⟩

variable (V) in

def bumpS : 𝓢(V, ℝ) :=
  (bumpData V).hasCompactSupport.toSchwartzMap (bumpData V).contDiff

theorem bumpS_coe : ((bumpS V : 𝓢(V, ℝ)) : V → ℝ) = (bumpData V : V → ℝ) := rfl

theorem bump_nonneg (y : V) : 0 ≤ (bumpData V) y := (bumpData V).nonneg

theorem bump_le_one (y : V) : (bumpData V) y ≤ 1 := (bumpData V).le_one

theorem bump_eq_one {y : V} (hy : ‖y‖ ≤ 2) : (bumpData V) y = 1 :=
  (bumpData V).one_of_mem_closedBall (by simp at hy ⊢; exact hy)

variable (g : 𝓢(V, ℂ)) (c : ℝ)

def level (n : ℕ) : ℝ :=
  ⨆ z : {z : V // c * (2 ^ n - 1) ≤ ‖z‖}, ‖g z.1‖

theorem level_nonneg (n : ℕ) : 0 ≤ level g c n :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_le_level {n : ℕ} {z : V} (hz : c * (2 ^ n - 1) ≤ ‖z‖) : ‖g z‖ ≤ level g c n := by
  have hb : BddAbove (Set.range fun w : {w : V // c * (2 ^ n - 1) ≤ ‖w‖} => ‖g w.1‖) := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 g, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact SchwartzMap.norm_le_seminorm ℝ g w.1
  exact le_ciSup (f := fun w : {w : V // c * (2 ^ n - 1) ≤ ‖w‖} => ‖g w.1‖) hb ⟨z, hz⟩

theorem exists_level_mul_pow_le (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, level g c n * ((2 : ℝ) ^ n) ^ N ≤ B := by
  set S : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) g with hS
  have hS0 : 0 ≤ S := by positivity
  have hdec : ∀ z : V, (1 + ‖z‖) ^ N * ‖g z‖ ≤ S := by
    intro z
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0)
      le_rfl le_rfl g z
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  refine ⟨(1 + c⁻¹) ^ N * S, by positivity, fun n => ?_⟩
  have hpow : 0 < ((2 : ℝ) ^ n) ^ N := by positivity
  rw [← le_div_iff₀ hpow]
  refine Real.iSup_le (fun w => ?_) (by positivity)
  obtain ⟨z, hz⟩ := w
  rw [le_div_iff₀ hpow]

  have h1 : (2 : ℝ) ^ n ≤ (1 + c⁻¹) * (1 + ‖z‖) := by
    have h2 : (2 : ℝ) ^ n - 1 ≤ c⁻¹ * ‖z‖ := by
      rw [le_inv_mul_iff₀' hc]
      linarith [hz, mul_comm c ((2 : ℝ) ^ n - 1)]
    nlinarith [norm_nonneg z, inv_pos.2 hc]
  have h3 : ((2 : ℝ) ^ n) ^ N ≤ (1 + c⁻¹) ^ N * (1 + ‖z‖) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 N
  calc ‖g z‖ * ((2 : ℝ) ^ n) ^ N ≤ ‖g z‖ * ((1 + c⁻¹) ^ N * (1 + ‖z‖) ^ N) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = (1 + c⁻¹) ^ N * ((1 + ‖z‖) ^ N * ‖g z‖) := by ring
    _ ≤ (1 + c⁻¹) ^ N * S := mul_le_mul_of_nonneg_left (hdec z) (by positivity)

theorem summable_level_mul_pow (hc : 0 < c) (k : ℕ) :
    Summable fun n : ℕ => level g c n * ((2 : ℝ) ^ n) ^ k := by
  obtain ⟨B, hB0, hB⟩ := exists_level_mul_pow_le g c hc (k + 1)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (level_nonneg g c n) (by positivity))
    (fun n => ?_) ((summable_geometric_two).mul_left B)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have h := hB n
  rw [pow_succ, ← mul_assoc] at h
  calc level g c n * ((2 : ℝ) ^ n) ^ k = level g c n * ((2 : ℝ) ^ n) ^ k * 2 ^ n * (1 / 2) ^ n := by
        rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ h2.ne', mul_one]
    _ ≤ B * (1 / 2) ^ n := mul_le_mul_of_nonneg_right h (by positivity)

theorem summable_level (hc : 0 < c) : Summable (level g c) := by
  simpa using summable_level_mul_pow g c hc 0

def term (n : ℕ) (y : V) : ℝ :=
  level g c n * (bumpData V) (((2 : ℝ) ^ n)⁻¹ • y)

theorem term_nonneg (n : ℕ) (y : V) : 0 ≤ term g c n y :=
  mul_nonneg (level_nonneg g c n) (bump_nonneg _)

theorem term_le_level (n : ℕ) (y : V) : term g c n y ≤ level g c n :=
  mul_le_of_le_one_right (level_nonneg g c n) (bump_le_one _)

theorem contDiff_bump_scaled (n : ℕ) :
    ContDiff ℝ ∞ (fun y : V => (bumpData V) (((2 : ℝ) ^ n)⁻¹ • y)) :=
  (bumpData V).contDiff.comp (contDiff_id.const_smul _)

theorem contDiff_term (n : ℕ) : ContDiff ℝ ∞ (term g c n) :=
  contDiff_const.mul (contDiff_bump_scaled n)

theorem norm_iteratedFDeriv_term_le (l n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ l (term g c n) x‖
      ≤ level g c n * ‖iteratedFDeriv ℝ l (bumpData V : V → ℝ) (((2 : ℝ) ^ n)⁻¹ • x)‖ := by
  have hsm : ContDiff ℝ l (fun y : V => (bumpData V) (((2 : ℝ) ^ n)⁻¹ • y)) :=
    (contDiff_bump_scaled n).of_le (mod_cast le_top)
  have h1 : iteratedFDeriv ℝ l (term g c n) x
      = level g c n • iteratedFDeriv ℝ l (fun y : V => (bumpData V) (((2 : ℝ) ^ n)⁻¹ • y)) x := by
    have : term g c n = fun y => level g c n • (fun y : V => (bumpData V) (((2 : ℝ) ^ n)⁻¹ • y)) y := by
      funext y; simp [term, smul_eq_mul]
    rw [this]
    exact iteratedFDeriv_const_smul_apply' hsm.contDiffAt
  have h2 : iteratedFDeriv ℝ l (fun y : V => (bumpData V) (((2 : ℝ) ^ n)⁻¹ • y)) x
      = (((2 : ℝ) ^ n)⁻¹) ^ l • iteratedFDeriv ℝ l (bumpData V : V → ℝ) (((2 : ℝ) ^ n)⁻¹ • x) := by
    have := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (f := (bumpData V : V → ℝ)) (i := l)
      (((2 : ℝ) ^ n)⁻¹) ((bumpData V).contDiff)
    exact congrFun this x
  rw [h1, h2, norm_smul, norm_smul, Real.norm_of_nonneg (level_nonneg g c n)]
  refine mul_le_mul_of_nonneg_left ?_ (level_nonneg g c n)
  have ha : ‖((((2 : ℝ) ^ n)⁻¹) ^ l : ℝ)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  calc ‖((((2 : ℝ) ^ n)⁻¹) ^ l : ℝ)‖ * ‖iteratedFDeriv ℝ l (bumpData V : V → ℝ) (((2 : ℝ) ^ n)⁻¹ • x)‖
      ≤ 1 * ‖iteratedFDeriv ℝ l (bumpData V : V → ℝ) (((2 : ℝ) ^ n)⁻¹ • x)‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_iteratedFDeriv_term_le' (l n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ l (term g c n) x‖ ≤ level g c n * SchwartzMap.seminorm ℝ 0 l (bumpS V) := by
  refine (norm_iteratedFDeriv_term_le g c l n x).trans (mul_le_mul_of_nonneg_left ?_ (level_nonneg g c n))
  have := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (bumpS V) l (((2 : ℝ) ^ n)⁻¹ • x)
  rwa [bumpS_coe] at this

theorem pow_mul_norm_iteratedFDeriv_term_le (k l n : ℕ) (x : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (term g c n) x‖
      ≤ level g c n * ((2 : ℝ) ^ n) ^ k * SchwartzMap.seminorm ℝ k l (bumpS V) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx : ‖x‖ = 2 ^ n * ‖((2 : ℝ) ^ n)⁻¹ • x‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg h2.le, ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul]
  have hsem := SchwartzMap.le_seminorm ℝ k l (bumpS V) (((2 : ℝ) ^ n)⁻¹ • x)
  rw [bumpS_coe] at hsem
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (term g c n) x‖
      ≤ ‖x‖ ^ k * (level g c n * ‖iteratedFDeriv ℝ l (bumpData V : V → ℝ) (((2 : ℝ) ^ n)⁻¹ • x)‖) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_term_le g c l n x) (by positivity)
    _ = level g c n * ((2 : ℝ) ^ n) ^ k
          * (‖((2 : ℝ) ^ n)⁻¹ • x‖ ^ k * ‖iteratedFDeriv ℝ l (bumpData V : V → ℝ) (((2 : ℝ) ^ n)⁻¹ • x)‖) := by
        rw [hx, mul_pow]; ring
    _ ≤ level g c n * ((2 : ℝ) ^ n) ^ k * SchwartzMap.seminorm ℝ k l (bumpS V) :=
        mul_le_mul_of_nonneg_left hsem (mul_nonneg (level_nonneg g c n) (by positivity))

def major (y : V) : ℝ := ∑' n : ℕ, term g c n y

theorem summable_term (hc : 0 < c) (y : V) : Summable fun n => term g c n y :=
  Summable.of_nonneg_of_le (fun n => term_nonneg g c n y) (fun n => term_le_level g c n y) (summable_level g c hc)

theorem major_nonneg (y : V) : 0 ≤ major g c y :=
  tsum_nonneg fun n => term_nonneg g c n y

theorem term_le_major (hc : 0 < c) (n : ℕ) (y : V) : term g c n y ≤ major g c y :=
  (summable_term g c hc y).le_tsum n fun j _ => term_nonneg g c j y

theorem contDiff_major (hc : 0 < c) : ContDiff ℝ ∞ (major g c) :=
  contDiff_tsum (N := ⊤) (f := term g c)
    (v := fun l n => level g c n * SchwartzMap.seminorm ℝ 0 l (bumpS V))
    (fun n => contDiff_term g c n)
    (fun l _ => (summable_level g c hc).mul_right _)
    (fun l n x _ => norm_iteratedFDeriv_term_le' g c l n x)

theorem iteratedFDeriv_major (hc : 0 < c) (l : ℕ) (x : V) :
    iteratedFDeriv ℝ l (major g c) x = ∑' n, iteratedFDeriv ℝ l (term g c n) x :=
  iteratedFDeriv_tsum_apply (N := ⊤) (f := term g c)
    (v := fun l n => level g c n * SchwartzMap.seminorm ℝ 0 l (bumpS V))
    (fun n => contDiff_term g c n)
    (fun l _ => (summable_level g c hc).mul_right _)
    (fun l n x _ => norm_iteratedFDeriv_term_le' g c l n x) le_top x

theorem decay_major (hc : 0 < c) (k l : ℕ) (x : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (major g c) x‖
      ≤ (∑' n : ℕ, level g c n * ((2 : ℝ) ^ n) ^ k) * SchwartzMap.seminorm ℝ k l (bumpS V) := by
  rw [iteratedFDeriv_major g c hc l x]
  have hsn : Summable fun n => ‖iteratedFDeriv ℝ l (term g c n) x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_iteratedFDeriv_term_le' g c l n x)
      ((summable_level g c hc).mul_right _)
  have hs2 : Summable fun n => level g c n * ((2 : ℝ) ^ n) ^ k * SchwartzMap.seminorm ℝ k l (bumpS V) :=
    (summable_level_mul_pow g c hc k).mul_right _
  have hs1 : Summable fun n => ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (term g c n) x‖ :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun n => pow_mul_norm_iteratedFDeriv_term_le g c k l n x) hs2
  calc ‖x‖ ^ k * ‖∑' n, iteratedFDeriv ℝ l (term g c n) x‖
      ≤ ‖x‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ l (term g c n) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsn) (by positivity)
    _ = ∑' n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (term g c n) x‖ := (hsn.tsum_mul_left _).symm
    _ ≤ ∑' n, level g c n * ((2 : ℝ) ^ n) ^ k * SchwartzMap.seminorm ℝ k l (bumpS V) :=
        hs1.tsum_le_tsum (fun n => pow_mul_norm_iteratedFDeriv_term_le g c k l n x) hs2
    _ = (∑' n : ℕ, level g c n * ((2 : ℝ) ^ n) ^ k) * SchwartzMap.seminorm ℝ k l (bumpS V) :=
        (summable_level_mul_pow g c hc k).tsum_mul_right _

def majorS (hc : 0 < c) : 𝓢(V, ℝ) where
  toFun := major g c
  smooth' := contDiff_major g c hc
  decay' k l := ⟨_, fun x => decay_major g c hc k l x⟩

theorem majorS_apply (hc : 0 < c) (y : V) : majorS g c hc y = major g c y := rfl

theorem norm_le_major (hc : 0 < c) {y z : V} (h : c * ‖y‖ ≤ ‖z‖) : ‖g z‖ ≤ major g c y := by
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := ‖y‖ + 1) (y := (2 : ℝ))
    (by linarith [norm_nonneg y]) one_lt_two
  have hz : c * (2 ^ n - 1) ≤ ‖z‖ :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hc.le) h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hb : (bumpData V) (((2 : ℝ) ^ n)⁻¹ • y) = 1 := by
    apply bump_eq_one
    rw [norm_smul, norm_inv, Real.norm_of_nonneg h2.le, inv_mul_le_iff₀ h2]
    rw [pow_succ] at hn2
    linarith
  calc ‖g z‖ ≤ level g c n := norm_le_level g c hz
    _ = term g c n y := by rw [term, hb, mul_one]
    _ ≤ major g c y := term_le_major g c hc n y

def majorC (hc : 0 < c) : 𝓢(V, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM (majorS g c hc)

theorem majorC_apply (hc : 0 < c) (y : V) : majorC g c hc y = ((major g c y : ℝ) : ℂ) := rfl

theorem exists_schwartz_envelope (hc : 0 < c) :
    ∃ G : 𝓢(V, ℂ), (∀ y, (((G y).re : ℝ) : ℂ) = G y ∧ 0 ≤ (G y).re) ∧
      ∀ y z : V, c * ‖y‖ ≤ ‖z‖ → ‖g z‖ ≤ (G y).re := by
  refine ⟨majorC g c hc, fun y => ?_, fun y z h => ?_⟩
  · rw [majorC_apply, Complex.ofReal_re]
    exact ⟨rfl, major_nonneg g c y⟩
  · rw [majorC_apply, Complex.ofReal_re]
    exact norm_le_major g c hc h

end SchwartzMajorantCore

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal AdeleRing"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "pureTensorSet2 schwartzBruhat2 tensor_mem_pureTensorSet2 mem_schwartzBruhat2_of_mem_pureTensorSet2 zero_mem_schwartzBruhat2 schwartzBruhat2_induction"
namespace K0cMajorant
p2m_open "NumberField.AdelicFourier NumberField"

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def archHom : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable (F) in

def finHom : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F :=
  RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

variable (F) in

def archProj (x : Fin 2 → AdeleRing (𝓞 F) F) : Fin 2 → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1

variable (F) in

def finProj (x : Fin 2 → AdeleRing (𝓞 F) F) : Fin 2 → FiniteAdeleRing (𝓞 F) F :=
  fun i => (x i).2

variable (F) in

def mapArch : AutomorphicForm.AdelicGL2 (𝓞 F) F →* GL (Fin 2) (mixedEmbedding.mixedSpace F) :=
  Matrix.GeneralLinearGroup.map (archHom F)

variable (F) in

def mapFin : AutomorphicForm.AdelicGL2 (𝓞 F) F →* GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.GeneralLinearGroup.map (finHom F)

theorem mapArch_apply (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    ((mapArch F g : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
        Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) i j
      = archHom F ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) :=
  Matrix.GeneralLinearGroup.map_apply (archHom F) i j g

theorem mapFin_apply (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) (i j : Fin 2) :
    ((mapFin F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 :=
  Matrix.GeneralLinearGroup.map_apply (finHom F) i j g

theorem archProj_vecMul (x : Fin 2 → AdeleRing (𝓞 F) F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    archProj F (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
      = Matrix.vecMul (archProj F x)
          ((mapArch F g : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
            Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) := by
  funext i
  have h := RingHom.map_vecMul (archHom F) (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) x i
  have h2 : ((mapArch F g : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))
      = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).map (archHom F) :=
    Matrix.ext fun i j => mapArch_apply g i j
  rw [h2]
  exact h

theorem finProj_vecMul (x : Fin 2 → AdeleRing (𝓞 F) F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F) :
    finProj F (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
      = Matrix.vecMul (finProj F x)
          ((mapFin F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
  funext i
  have h := RingHom.map_vecMul (finHom F) (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) x i
  have h2 : ((mapFin F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).map (finHom F) :=
    Matrix.ext fun i j => mapFin_apply g i j
  rw [h2]
  exact h

theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

theorem continuous_archHom : Continuous (archHom F) :=
  continuous_ringEquiv_mixedSpace.comp continuous_fst

theorem continuous_map_of_continuous {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : AdeleRing (𝓞 F) F →+* S) (hφ : Continuous φ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) φ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ (Matrix.GeneralLinearGroup.map (n := Fin 2) φ))
        = fun g : AutomorphicForm.AdelicGL2 (𝓞 F) F =>
          (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).map φ := by
      funext g; exact Matrix.ext fun i j => Matrix.GeneralLinearGroup.map_apply φ i j g
    rw [this]
    exact Units.continuous_val.matrix_map hφ
  · have : (fun g : AutomorphicForm.AdelicGL2 (𝓞 F) F =>
          ((Matrix.GeneralLinearGroup.map (n := Fin 2) φ g)⁻¹ : GL (Fin 2) S).val)
        = fun g : AutomorphicForm.AdelicGL2 (𝓞 F) F =>
          ((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).map φ := by
      funext g
      rw [← map_inv]
      exact Matrix.ext fun i j => Matrix.GeneralLinearGroup.map_apply φ i j g⁻¹
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_map hφ

theorem continuous_mapArch : Continuous (mapArch F) :=
  continuous_map_of_continuous (archHom F) continuous_archHom

theorem continuous_mapFin : Continuous (mapFin F) :=
  continuous_map_of_continuous (finHom F) continuous_snd

def entrySum (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖

theorem entrySum_nonneg (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) : 0 ≤ entrySum M := by
  unfold entrySum; positivity

theorem norm_vecMul_le (y : Fin 2 → mixedEmbedding.mixedSpace F)
    (M : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) :
    ‖Matrix.vecMul y M‖ ≤ entrySum M * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity [entrySum_nonneg M])).2 fun j => ?_
  have hj : Matrix.vecMul y M j = ∑ i, y i * M i j := rfl
  rw [hj]
  calc ‖∑ i, y i * M i j‖ ≤ ∑ i, ‖y i * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖y‖ * ‖M i j‖ := Finset.sum_le_sum fun i _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm y i) (norm_nonneg _))
    _ = (∑ i, ‖M i j‖) * ‖y‖ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ ≤ entrySum M * ‖y‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (f := fun j => ‖M i j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)

def invSize (k : AutomorphicForm.AdelicGL2 (𝓞 F) F) : ℝ :=
  entrySum (((mapArch F k)⁻¹ : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
    Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))

theorem continuous_invSize : Continuous (invSize (F := F)) := by
  unfold invSize entrySum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  refine Continuous.norm ?_
  exact (Continuous.matrix_elem (Units.continuous_val.comp (continuous_inv.comp continuous_mapArch)) i j)

theorem norm_le_invSize_mul (k : AutomorphicForm.AdelicGL2 (𝓞 F) F) (y : Fin 2 → mixedEmbedding.mixedSpace F) :
    ‖y‖ ≤ invSize k * ‖Matrix.vecMul y ((mapArch F k : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))‖ := by
  have h : y = Matrix.vecMul (Matrix.vecMul y ((mapArch F k : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)))
      (((mapArch F k)⁻¹ : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
        Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)) := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  conv_lhs => rw [h]
  exact norm_vecMul_le _ _

theorem exists_uniform_lower_bound {K : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ k ∈ K, ∀ y : Fin 2 → mixedEmbedding.mixedSpace F,
      c * ‖y‖ ≤ ‖Matrix.vecMul y ((mapArch F k : GL (Fin 2) (mixedEmbedding.mixedSpace F)) :
        Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))‖ := by
  obtain ⟨L₀, hL₀⟩ := (hK.bddAbove_image continuous_invSize.continuousOn)
  set L : ℝ := max L₀ 1 with hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨L⁻¹, inv_pos.2 hLpos, fun k hk y => ?_⟩
  have h1 : invSize k ≤ L := (hL₀ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have h2 := norm_le_invSize_mul k y
  rw [inv_mul_le_iff₀ hLpos]
  exact h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))

theorem exists_nhds_forall_vecMul_eq {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {H : (Fin 2 → R) → ℂ} (hlc : IsLocallyConstant H) (hcs : HasCompactSupport H) :
    ∃ V ∈ 𝓝 (1 : GL (Fin 2) R), ∀ u ∈ V, ∀ w : Fin 2 → R,
      H (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R)) = H w := by
  have hact : Continuous fun p : (Fin 2 → R) × GL (Fin 2) R =>
      Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R) :=
    Continuous.matrix_vecMul continuous_fst (Units.continuous_val.comp continuous_snd)
  set Z : Set ((Fin 2 → R) × GL (Fin 2) R) :=
    {p | H (Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R)) = H p.1} with hZ
  have hZopen : IsOpen Z := by
    have h1 : IsLocallyConstant fun p : (Fin 2 → R) × GL (Fin 2) R =>
        (H (Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R)), H p.1) :=
      (hlc.comp_continuous hact).prodMk (hlc.comp_continuous continuous_fst)
    have : Z = (fun p : (Fin 2 → R) × GL (Fin 2) R =>
        (H (Matrix.vecMul p.1 (p.2 : Matrix (Fin 2) (Fin 2) R)), H p.1)) ⁻¹' {q | q.1 = q.2} := by
      ext p; simp [hZ]
    rw [this]
    exact h1 _
  set K : Set (Fin 2 → R) := tsupport H with hK
  have hKc : IsCompact K := hcs
  have hsub : K ×ˢ ({1} : Set (GL (Fin 2) R)) ⊆ Z := by
    rintro ⟨w, u⟩ ⟨_, hu⟩
    have hu1 : u = 1 := hu
    subst hu1
    show H (Matrix.vecMul w ((1 : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) = H w
    rw [Units.val_one, Matrix.vecMul_one]
  obtain ⟨U, V, hU, hV, hKU, h1V, hUV⟩ := generalized_tube_lemma hKc isCompact_singleton hZopen hsub
  have h1V' : (1 : GL (Fin 2) R) ∈ V := h1V (Set.mem_singleton 1)
  refine ⟨V ∩ (fun u => u⁻¹) ⁻¹' V, ?_, ?_⟩
  · refine Filter.inter_mem (hV.mem_nhds h1V') ?_
    exact continuous_inv.continuousAt.preimage_mem_nhds (by rw [inv_one]; exact hV.mem_nhds h1V')
  · rintro u ⟨huV, huV'⟩ w
    by_cases hw : w ∈ K
    · exact hUV (Set.mk_mem_prod (hKU hw) huV)
    · have hw0 : H w = 0 := image_eq_zero_of_notMem_tsupport hw
      rw [hw0]
      by_contra hne
      have hmem : Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R) ∈ K :=
        subset_tsupport H (Function.mem_support.mpr hne)
      have hz : (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R), u⁻¹) ∈ Z :=
        hUV (Set.mk_mem_prod (hKU hmem) huV')
      have hz' : H (Matrix.vecMul (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R))
          ((u⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
          = H (Matrix.vecMul w (u : Matrix (Fin 2) (Fin 2) R)) := hz
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at hz'
      exact hne (hz'.symm.trans hw0)

def vecMulHomeomorph {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : GL (Fin 2) R) : (Fin 2 → R) ≃ₜ (Fin 2 → R) where
  toFun y := Matrix.vecMul y (M : Matrix (Fin 2) (Fin 2) R)
  invFun y := Matrix.vecMul y ((M⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  left_inv y := by
    show Matrix.vecMul (Matrix.vecMul y (M : Matrix (Fin 2) (Fin 2) R))
        ((M⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = y
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv y := by
    show Matrix.vecMul (Matrix.vecMul y ((M⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
        (M : Matrix (Fin 2) (Fin 2) R) = y
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

theorem normComp_locallyConstant_compactSupport {h : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) (M : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    IsLocallyConstant (fun w => ((‖h (Matrix.vecMul w (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖ : ℝ) : ℂ)) ∧
    HasCompactSupport (fun w => ((‖h (Matrix.vecMul w (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖ : ℝ) : ℂ)) := by
  have h1 : IsLocallyConstant fun w => h (Matrix.vecMul w (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    hlc.comp_continuous (vecMulHomeomorph M).continuous
  have h2 : HasCompactSupport fun w => h (Matrix.vecMul w (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    hcs.comp_homeomorph (vecMulHomeomorph M)
  exact ⟨h1.comp (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)), h2.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp)⟩

def IsRealNonneg (Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∀ x, (((Ψ x).re : ℝ) : ℂ) = Ψ x ∧ 0 ≤ (Ψ x).re

def HasMajorant (K : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ, Ψ ∈ schwartzBruhat2 F ∧ IsRealNonneg Ψ ∧
    ∀ k ∈ K, ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
      ‖Φ (Matrix.vecMul x (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖ ≤ (Ψ x).re

theorem hasMajorant_zero (K : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) :
    HasMajorant K (0 : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) :=
  ⟨0, zero_mem_schwartzBruhat2, fun x => by simp, fun k _ x => by simp⟩

theorem HasMajorant.add {K : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} {Φ₁ Φ₂ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (h₁ : HasMajorant K Φ₁) (h₂ : HasMajorant K Φ₂) : HasMajorant K (Φ₁ + Φ₂) := by
  obtain ⟨Ψ₁, hΨ₁, hr₁, hd₁⟩ := h₁
  obtain ⟨Ψ₂, hΨ₂, hr₂, hd₂⟩ := h₂
  refine ⟨Ψ₁ + Ψ₂, Submodule.add_mem _ hΨ₁ hΨ₂, fun x => ?_, fun k hk x => ?_⟩
  · obtain ⟨e₁, p₁⟩ := hr₁ x
    obtain ⟨e₂, p₂⟩ := hr₂ x
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, Complex.add_re, Complex.ofReal_add, e₁, e₂]
    · simp only [Pi.add_apply, Complex.add_re]; positivity
  · simp only [Pi.add_apply, Complex.add_re]
    exact (norm_add_le _ _).trans (add_le_add (hd₁ k hk x) (hd₂ k hk x))

theorem HasMajorant.smul {K : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ}
    (h : HasMajorant K Φ) (a : ℂ) : HasMajorant K (a • Φ) := by
  obtain ⟨Ψ, hΨ, hr, hd⟩ := h
  refine ⟨((‖a‖ : ℝ) : ℂ) • Ψ, Submodule.smul_mem _ _ hΨ, fun x => ?_, fun k hk x => ?_⟩
  · obtain ⟨e, p⟩ := hr x
    have hx : (((‖a‖ : ℝ) : ℂ) • Ψ) x = (((‖a‖ * (Ψ x).re : ℝ)) : ℂ) := by
      simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]; rw [e]
    rw [hx, Complex.ofReal_re]
    exact ⟨rfl, mul_nonneg (norm_nonneg a) p⟩
  · obtain ⟨e, p⟩ := hr x
    have hx : (((‖a‖ : ℝ) : ℂ) • Ψ) x = (((‖a‖ * (Ψ x).re : ℝ)) : ℂ) := by
      simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]; rw [e]
    rw [hx, Complex.ofReal_re, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hd k hk x) (norm_nonneg a)

theorem tensorTerm_mem (G : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ))
    {h : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (M : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
        G (archProj F x) * ((‖h (Matrix.vecMul (finProj F x) (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖ : ℝ) : ℂ))
      ∈ schwartzBruhat2 F := by
  obtain ⟨h1, h2⟩ := normComp_locallyConstant_compactSupport hlc hcs M
  exact mem_schwartzBruhat2_of_mem_pureTensorSet2 (tensor_mem_pureTensorSet2 G _ h1 h2)

theorem hasMajorant_of_mem_pureTensorSet2 {K : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hK : IsCompact K)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ pureTensorSet2 F) : HasMajorant K Φ := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hΦ

  obtain ⟨c, hc, hlow⟩ := exists_uniform_lower_bound hK
  obtain ⟨G, hGr, hGd⟩ := SchwartzMajorantCore.exists_schwartz_envelope g c hc

  obtain ⟨V, hV, hinv⟩ := exists_nhds_forall_vecMul_eq hlc hcs
  set U : AutomorphicForm.AdelicGL2 (𝓞 F) F → Set (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
    fun k₀ => (fun k => (mapFin F k₀)⁻¹ * mapFin F k) ⁻¹' V with hU
  have hUn : ∀ k₀ ∈ K, U k₀ ∈ 𝓝 k₀ := by
    intro k₀ _
    have hc' : Continuous fun k : AutomorphicForm.AdelicGL2 (𝓞 F) F => (mapFin F k₀)⁻¹ * mapFin F k :=
      continuous_const.mul continuous_mapFin
    refine hc'.continuousAt.preimage_mem_nhds ?_
    rw [inv_mul_cancel]
    exact hV
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover U hUn

  set T : AutomorphicForm.AdelicGL2 (𝓞 F) F → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ := fun k₀ x =>
    G (archProj F x) * ((‖h (Matrix.vecMul (finProj F x)
      ((mapFin F k₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖ : ℝ) : ℂ)
    with hT
  have hTre : ∀ k₀ x, T k₀ x = ((((G (archProj F x)).re
      * ‖h (Matrix.vecMul (finProj F x)
        ((mapFin F k₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖ : ℝ)) : ℂ) := by
    intro k₀ x
    rw [hT]
    simp only [Complex.ofReal_mul]
    rw [(hGr (archProj F x)).1]
  refine ⟨∑ k₀ ∈ t, T k₀, Submodule.sum_mem _ fun k₀ _ => tensorTerm_mem G hlc hcs (mapFin F k₀), fun x => ?_,
    fun k hk x => ?_⟩
  · rw [Finset.sum_apply]
    simp_rw [hTre]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
    exact ⟨rfl, Finset.sum_nonneg fun k₀ _ => mul_nonneg (hGr _).2 (norm_nonneg _)⟩
  ·
    have hk' := hcov hk
    simp only [Set.mem_iUnion] at hk'
    obtain ⟨k₀, hk₀t, hkU⟩ := hk'
    have hu : (mapFin F k₀)⁻¹ * mapFin F k ∈ V := hkU

    have hval : (fun x : Fin 2 → AdeleRing (𝓞 F) F =>
          g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * h (fun i => (x i).2))
          (Matrix.vecMul x (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
        = g (Matrix.vecMul (archProj F x)
              ((mapArch F k : GL (Fin 2) (mixedEmbedding.mixedSpace F)) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)))
          * h (Matrix.vecMul (finProj F x)
              ((mapFin F k₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
      show g (archProj F (Matrix.vecMul x (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
          * h (finProj F (Matrix.vecMul x (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) = _
      rw [archProj_vecMul, finProj_vecMul]
      congr 1
      have hfac : mapFin F k = mapFin F k₀ * ((mapFin F k₀)⁻¹ * mapFin F k) := by
        rw [mul_inv_cancel_left]
      conv_lhs => rw [hfac, Units.val_mul, ← Matrix.vecMul_vecMul]
      exact hinv _ hu _
    rw [hval, norm_mul, Finset.sum_apply]
    simp_rw [hTre]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
    calc ‖g (Matrix.vecMul (archProj F x)
              ((mapArch F k : GL (Fin 2) (mixedEmbedding.mixedSpace F)) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F)))‖
          * ‖h (Matrix.vecMul (finProj F x)
              ((mapFin F k₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖
        ≤ (G (archProj F x)).re
          * ‖h (Matrix.vecMul (finProj F x)
              ((mapFin F k₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖ :=
          mul_le_mul_of_nonneg_right (hGd _ _ (hlow k hk (archProj F x))) (norm_nonneg _)
      _ ≤ ∑ k₁ ∈ t, (G (archProj F x)).re
          * ‖h (Matrix.vecMul (finProj F x)
              ((mapFin F k₁ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖ :=
          Finset.single_le_sum (f := fun k₁ => (G (archProj F x)).re
            * ‖h (Matrix.vecMul (finProj F x)
              ((mapFin F k₁ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))‖)
            (fun k₁ _ => mul_nonneg (hGr _).2 (norm_nonneg _)) hk₀t

theorem hasMajorant_of_mem_schwartzBruhat2 {K : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hK : IsCompact K)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) : HasMajorant K Φ := by
  induction hΦ using schwartzBruhat2_induction with
  | tensor Φ hΦ => exact hasMajorant_of_mem_pureTensorSet2 hK hΦ
  | zero => exact hasMajorant_zero K
  | add Φ Ψ _ _ ihΦ ihΨ => exact ihΦ.add ihΨ
  | smul a Φ _ ih => exact ih.smul a

end NumberField.AdelicFourier.K0cMajorant

end

open _root_.NumberField _root_.P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact.NumberField _root_.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact.NumberField.AdelicFourier AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (K : Set (AdelicGL2 (𝓞 F) F)) (hK : IsCompact K) :
    ∃ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ, Ψ ∈ schwartzBruhat2 F ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, (((Ψ x).re : ℝ) : ℂ) = Ψ x ∧ 0 ≤ (Ψ x).re) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, ‖Φ x‖ ≤ (Ψ x).re) ∧
      ∀ g ∈ K, ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
        ‖Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖ ≤ (Ψ x).re := by
  obtain ⟨Ψ, hΨ, hr, hd⟩ :=
    NumberField.AdelicFourier.K0cMajorant.hasMajorant_of_mem_schwartzBruhat2 (hK.insert 1) hΦ
  refine ⟨Ψ, hΨ, hr, fun x => ?_, fun g hg x => hd g (Set.mem_insert_of_mem _ hg) x⟩
  have h := hd 1 (Set.mem_insert _ _) x
  rwa [Units.val_one, Matrix.vecMul_one] at h

end S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact (solution)
