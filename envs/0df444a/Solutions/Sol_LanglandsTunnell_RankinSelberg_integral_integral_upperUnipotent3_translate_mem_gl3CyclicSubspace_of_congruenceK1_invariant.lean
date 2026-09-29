-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/581edc21-e350-5f0f-a1ec-457c52ce078f

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

namespace Ws46
namespace E2

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.CubicInduction Topology

variable (p : HeightOneSpectrum (𝓞 ℚ))
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]

def paramSubgroup (U : Subgroup (LocalGL3 p)) (n : A → LocalGL3 p)
    (hn_add : ∀ a b, n (a + b) = n a * n b) (hn0 : n 0 = 1) : AddSubgroup A where
  carrier := {z | n z ∈ U}
  add_mem' := fun {a b} ha hb => by show n (a + b) ∈ U; rw [hn_add]; exact U.mul_mem ha hb
  zero_mem' := by show n 0 ∈ U; rw [hn0]; exact U.one_mem
  neg_mem' := fun {a} ha => by
    show n (-a) ∈ U
    have : n (-a) = (n a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hn_add, neg_add_cancel, hn0]
    rw [this]; exact U.inv_mem ha

set_option maxHeartbeats 3200000 in

theorem exists_finset_integral_eq_sum
    (W : LocalGL3 p → ℂ) (U : Subgroup (LocalGL3 p)) (hU : IsOpen (U : Set (LocalGL3 p)))
    (hW : ∀ k ∈ U, ∀ g : LocalGL3 p, W (g * k) = W g)
    (n : A → LocalGL3 p) (hn_add : ∀ a b, n (a + b) = n a * n b) (hn0 : n 0 = 1) (hn : Continuous n)
    (Φ : A → ℂ) (hΦc : HasCompactSupport Φ) (ν : Measure A) (hΦi : Integrable Φ ν) :
    ∃ (s : Finset A) (a : A → ℂ),
      ∀ g : LocalGL3 p, Integrable (fun z => W (g * n z) * Φ z) ν ∧
        ∫ z, W (g * n z) * Φ z ∂ν = ∑ t ∈ s, a t * W (g * n t) := by
  classical
  set L := paramSubgroup p U n hn_add hn0 with hL
  have hLo : IsOpen (L : Set A) := hU.preimage hn
  haveI : DiscreteTopology (A ⧸ L) := QuotientAddGroup.discreteTopology hLo
  set K := tsupport Φ with hK
  have hKc : IsCompact K := hΦc
  set q : A → A ⧸ L := QuotientAddGroup.mk with hq
  have hqc : Continuous q := QuotientAddGroup.continuous_mk
  have hfin : (q '' K).Finite := (hKc.image hqc).finite_of_discrete
  set S : Finset (A ⧸ L) := hfin.toFinset with hS
  choose rep hrep using fun c : A ⧸ L => QuotientAddGroup.mk_surjective c
  refine ⟨S.image rep, fun t => ∫ z in K ∩ q ⁻¹' {q t}, Φ z ∂ν, fun g => ?_⟩
  have hconst : ∀ (c : A ⧸ L) (z : A), q z = c → W (g * n z) = W (g * n (rep c)) := by
    intro c z hz
    have hmem : -(rep c) + z ∈ L := by
      rw [← QuotientAddGroup.eq]; rw [hrep c]; exact hz.symm
    have : z = rep c + (-(rep c) + z) := by abel
    rw [this, hn_add, ← mul_assoc, hW _ hmem]
  have hzero : ∀ z, z ∉ K → W (g * n z) * Φ z = 0 := by
    intro z hz; rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hKm : MeasurableSet K := (isClosed_tsupport Φ).measurableSet
  have hfib : ∀ c : A ⧸ L, MeasurableSet (K ∩ q ⁻¹' {c}) := fun c =>
    hKm.inter ((isOpen_discrete {c}).preimage hqc).measurableSet
  have hcover : K = ⋃ c ∈ S, (K ∩ q ⁻¹' {c}) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, exists_and_left, exists_prop]
    constructor
    · intro hz; exact ⟨hz, q z, by rw [hS, Set.Finite.mem_toFinset]; exact ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨hz, _, _, _⟩; exact hz
  have hdisj : (↑S : Set (A ⧸ L)).Pairwise (Function.onFun Disjoint fun c => K ∩ q ⁻¹' {c}) := by
    intro c _ c' _ hcc'
    refine Set.disjoint_left.2 fun z hz hz' => hcc' ?_
    exact hz.2.symm.trans hz'.2
  have hpiece : ∀ c : A ⧸ L, IntegrableOn (fun z => W (g * n z) * Φ z) (K ∩ q ⁻¹' {c}) ν := by
    intro c
    have : IntegrableOn (fun z => W (g * n (rep c)) * Φ z) (K ∩ q ⁻¹' {c}) ν := (hΦi.const_mul _).integrableOn
    exact this.congr_fun (fun z hz => by rw [hconst c z hz.2]) (hfib c)
  have hinj : ∀ c ∈ S, ∀ c' ∈ S, rep c = rep c' → c = c' := by
    intro c _ c' _ h; rw [← hrep c, ← hrep c', h]
  refine ⟨?_, ?_⟩
  ·
    have hK' : IntegrableOn (fun z => W (g * n z) * Φ z) K ν := by
      rw [hcover]; exact integrableOn_finset_iUnion.2 fun c _ => hpiece c
    refine hK'.integrable_of_forall_notMem_eq_zero ?_
    intro z hz; exact hzero z hz
  symm
  calc ∑ t ∈ S.image rep, (fun t => ∫ z in K ∩ q ⁻¹' {q t}, Φ z ∂ν) t * W (g * n t)
      = ∑ c ∈ S, (∫ z in K ∩ q ⁻¹' {q (rep c)}, Φ z ∂ν) * W (g * n (rep c)) := Finset.sum_image hinj
    _ = ∑ c ∈ S, ∫ z in K ∩ q ⁻¹' {c}, W (g * n z) * Φ z ∂ν := by
        refine Finset.sum_congr rfl fun c hc => ?_
        have hq : q (rep c) = c := hrep c
        rw [hq, mul_comm, ← integral_const_mul]
        refine setIntegral_congr_fun (hfib c) fun z hz => ?_
        rw [hconst c z hz.2]
    _ = ∫ z in ⋃ c ∈ S, (K ∩ q ⁻¹' {c}), W (g * n z) * Φ z ∂ν :=
        (integral_biUnion_finset S (fun c _ => hfib c) hdisj (fun c _ => hpiece c)).symm
    _ = ∫ z in K, W (g * n z) * Φ z ∂ν := by rw [← hcover]
    _ = ∫ z, W (g * n z) * Φ z ∂ν := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hzero z hz)

end Ws46.E2

namespace Ws46
namespace E2

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Topology Filter

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem eventually_valued_sub_le (c : p.adicCompletion ℚ) (n : ℕ) :
    ∀ᶠ y in 𝓝 c, Valued.v (y - c) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ : ∃ π : p.adicCompletion ℚ, Valued.v π = WithZero.exp (-(1 : ℤ)) :=
    ⟨(NumberField.AdelicLevel.uniformizerUnit ℚ p : p.adicCompletion ℚ), NumberField.AdelicLevel.valued_uniformizerUnit ℚ p⟩
  have hπ0 : π ^ n ≠ 0 := by
    apply pow_ne_zero; intro h; rw [h, map_zero] at hπ; exact WithZero.coe_ne_zero.symm hπ
  have hvπn : Valued.v (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  have h0 : Tendsto (fun y : p.adicCompletion ℚ => y - c) (𝓝 c) (𝓝 0) := by
    have := ((continuous_sub_right c).tendsto c)
    rwa [sub_self] at this
  filter_upwards [h0.eventually (eventually_valued_lt p hπ0)] with y hy
  rw [hvπn] at hy
  exact hy.le

theorem congruenceK1_mem_nhds_one (f : ℕ) : congruenceK1 (𝓞 ℚ) ℚ p f ∈ 𝓝 (1 : LocalGL3 p) := by
  have hent : ∀ (φ : LocalGL3 p → LocalGL3 p), Continuous φ → φ 1 = 1 → ∀ (i j : Fin 3) (n : ℕ),
      ∀ᶠ k in 𝓝 (1 : LocalGL3 p), Valued.v (((φ k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(n : ℤ)) := by
    intro φ hφ h1 i j n
    have hc : Continuous fun k : LocalGL3 p => ((φ k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j :=
      (Units.continuous_val.matrix_elem i j).comp hφ
    have := (hc.tendsto 1).eventually (eventually_valued_sub_le p ((((φ 1 : LocalGL3 p)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) n)
    rw [h1] at this
    simpa only [Units.val_one] using this
  have hle1 : ∀ (φ : LocalGL3 p → LocalGL3 p), Continuous φ → φ 1 = 1 → ∀ (i j : Fin 3),
      ∀ᶠ k in 𝓝 (1 : LocalGL3 p), Valued.v (((φ k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1 := by
    intro φ hφ h1 i j
    filter_upwards [hent φ hφ h1 i j 0] with k hk
    have h1' : Valued.v ((1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1 := by
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne hij, map_zero]; exact zero_le'
    have : Valued.v ((((φ k : LocalGL3 p)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j - (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j + (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1 :=
      (Valuation.map_add _ _ _).trans (max_le (hk.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega))) h1')
    rwa [sub_add_cancel] at this
  have hall : ∀ᶠ (k : LocalGL3 p) in 𝓝 (1 : LocalGL3 p),
      (∀ i j : Fin 3, Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1) ∧
      (∀ i j : Fin 3, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1) ∧
      Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 0) ≤ WithZero.exp (-(f : ℤ)) ∧
      Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 1) ≤ WithZero.exp (-(f : ℤ)) ∧
      Valued.v (((k : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 2 - 1) ≤ WithZero.exp (-(f : ℤ)) := by
    refine ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hle1 id continuous_id rfl i j).and
      ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hle1 (fun k => k⁻¹) continuous_inv inv_one i j).and
      ((hent id continuous_id rfl 2 0 f).and ((hent id continuous_id rfl 2 1 f).and (hent id continuous_id rfl 2 2 f))))).mono ?_
    intro k hk
    refine ⟨hk.1, hk.2.1, ?_, ?_, ?_⟩
    · simpa [Matrix.one_apply_ne] using hk.2.2.1
    · simpa [Matrix.one_apply_ne] using hk.2.2.2.1
    · simpa [Matrix.one_apply_eq] using hk.2.2.2.2
  exact Filter.mem_of_superset hall fun k hk => ⟨⟨hk.1, hk.2.1⟩, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2⟩

theorem exists_open_stabiliser (f : ℕ) (W₀ : LocalGL3 p → ℂ)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g) :
    ∃ U : Subgroup (LocalGL3 p), IsOpen (U : Set (LocalGL3 p)) ∧ ∀ k ∈ U, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g := by
  let U : Subgroup (LocalGL3 p) :=
    { carrier := {k | ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g}
      mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
      one_mem' := fun g => by rw [mul_one]
      inv_mem' := fun {a} ha g => by rw [← ha (g * a⁻¹), inv_mul_cancel_right] }
  refine ⟨U, ?_, fun k hk g => hk g⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  exact Filter.mem_of_superset (congruenceK1_mem_nhds_one p f) fun k hk => hK1 k hk

theorem n_split (u y : p.adicCompletion ℚ) : (upperUnipotent3 u 0 y : LocalGL3 p) = upperUnipotent3 u 0 0 * upperUnipotent3 0 0 y := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Fin.sum_univ_three]

theorem n_split' (u y : p.adicCompletion ℚ) : (upperUnipotent3 u 0 y : LocalGL3 p) = upperUnipotent3 0 0 y * upperUnipotent3 u 0 0 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Fin.sum_univ_three]

theorem n₁_add (a b : p.adicCompletion ℚ) : (upperUnipotent3 0 0 (a + b) : LocalGL3 p) = upperUnipotent3 0 0 a * upperUnipotent3 0 0 b := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem n₂_add (a b : p.adicCompletion ℚ) : (upperUnipotent3 (a + b) 0 0 : LocalGL3 p) = upperUnipotent3 a 0 0 * upperUnipotent3 b 0 0 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem n_zero : (upperUnipotent3 0 0 0 : LocalGL3 p) = 1 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

theorem continuous_n₁ : Continuous fun y : p.adicCompletion ℚ => (upperUnipotent3 0 0 y : LocalGL3 p) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> first | exact continuous_const | exact continuous_id
  · have : (fun y : p.adicCompletion ℚ => (((upperUnipotent3 0 0 y : LocalGL3 p))⁻¹ : LocalGL3 p).val) =
        fun y : p.adicCompletion ℚ => (upperUnipotent3 0 0 y : LocalGL3 p).inv := by funext y; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;>
      first | exact continuous_const | exact continuous_id | exact continuous_neg | (exact (continuous_const.mul continuous_id).sub continuous_const)

theorem continuous_n₂ : Continuous fun u : p.adicCompletion ℚ => (upperUnipotent3 u 0 0 : LocalGL3 p) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> first | exact continuous_const | exact continuous_id
  · have : (fun u : p.adicCompletion ℚ => (((upperUnipotent3 u 0 0 : LocalGL3 p))⁻¹ : LocalGL3 p).val) =
        fun u : p.adicCompletion ℚ => (upperUnipotent3 u 0 0 : LocalGL3 p).inv := by funext u; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;>
      first | exact continuous_const | exact continuous_id | exact continuous_neg | (exact (continuous_id.mul continuous_const).sub continuous_const)

end Ws46.E2

namespace Ws46
namespace E2

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Topology Filter

scoped instance isFiniteMeasureOnCompacts_selfDualHaarAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    @IsFiniteMeasureOnCompacts _ (localBorel ℚ p) _ (selfDualHaarAt ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  infer_instance

set_option maxHeartbeats 6400000 in
theorem main
    (p : HeightOneSpectrum (𝓞 ℚ)) (f : ℕ)
    (W₀ : LocalGL3 p → ℂ)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ)
    (hφ₁ : IsLocallyConstant φ₁) (hφ₁c : HasCompactSupport φ₁) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    (fun g : LocalGL3 p =>
        ∫ u, ∫ y, W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) ∈
      gl3CyclicSubspace W₀ := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  obtain ⟨U, hUo, hUW⟩ := exists_open_stabiliser p f W₀ hK1
  have hφi : Integrable φ (selfDualHaarAt ℚ p) := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hφ₁i : Integrable φ₁ (selfDualHaarAt ℚ p) := hφ₁.continuous.integrable_of_hasCompactSupport hφ₁c
  obtain ⟨s₁, a₁, h₁⟩ := exists_finset_integral_eq_sum p W₀ U hUo hUW (fun y : p.adicCompletion ℚ => (upperUnipotent3 0 0 y : LocalGL3 p))
    (fun a b => n₁_add p a b) (n_zero p) (continuous_n₁ p) φ₁ hφ₁c (selfDualHaarAt ℚ p) hφ₁i
  obtain ⟨s₂, a₂, h₂⟩ := exists_finset_integral_eq_sum p W₀ U hUo hUW (fun u : p.adicCompletion ℚ => (upperUnipotent3 u 0 0 : LocalGL3 p))
    (fun a b => n₂_add p a b) (n_zero p) (continuous_n₂ p) φ hφc (selfDualHaarAt ℚ p) hφi
  have hcomm : ∀ (g : LocalGL3 p) (u t : p.adicCompletion ℚ),
      g * upperUnipotent3 u 0 0 * upperUnipotent3 0 0 t = g * upperUnipotent3 0 0 t * upperUnipotent3 u 0 0 := by
    intro g u t; rw [mul_assoc, mul_assoc, ← n_split, n_split']
  have hinner : ∀ (g : LocalGL3 p) (u : p.adicCompletion ℚ),
      ∫ y, W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) =
        ∑ t ∈ s₁, a₁ t * (W₀ (g * upperUnipotent3 0 0 t * upperUnipotent3 u 0 0) * φ u) := by
    intro g u
    have : (fun y => W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y)) =
        fun y => φ u * (W₀ ((g * upperUnipotent3 u 0 0) * upperUnipotent3 0 0 y) * φ₁ y) := by
      funext y; rw [n_split, mul_assoc]; ring
    rw [this, integral_const_mul, (h₁ (g * upperUnipotent3 u 0 0)).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hcomm]; ring
  have houter : ∀ g : LocalGL3 p,
      ∫ u, ∫ y, W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p) =
        ∑ t ∈ s₁, a₁ t * ∑ r ∈ s₂, a₂ r * W₀ (g * upperUnipotent3 0 0 t * upperUnipotent3 r 0 0) := by
    intro g
    simp_rw [hinner g]
    rw [integral_finset_sum _ (fun t _ => ((h₂ (g * upperUnipotent3 0 0 t)).1.const_mul (a₁ t)))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_const_mul, (h₂ (g * upperUnipotent3 0 0 t)).2]
  have hfun : (fun g : LocalGL3 p =>
      ∫ u, ∫ y, W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p)) =
      ∑ t ∈ s₁, ∑ r ∈ s₂, (a₁ t * a₂ r) •
        gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 0 t * upperUnipotent3 r 0 0 : LocalGL3 p) W₀ := by
    funext g
    rw [houter g, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, gl3AmbientRightTranslate_apply, mul_assoc]
  rw [hfun]
  exact Submodule.sum_mem _ fun t _ => Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Ws46.E2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant.Ws46 P2MW.S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant.Ws46.E2"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant.Ws46"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (f : ℕ)
    (W₀ : LocalGL3 p → ℂ)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    (fun g : LocalGL3 p =>
        ∫ u, ∫ y, W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) ∈
      gl3CyclicSubspace W₀ :=
  Ws46.E2.main p f W₀ hK1 φ φ₁ hφ.1 hφ.2 hφ₁.1 hφ₁.2

end S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant (solution)
