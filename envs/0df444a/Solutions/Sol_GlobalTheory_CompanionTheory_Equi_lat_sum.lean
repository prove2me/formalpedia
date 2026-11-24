-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.lat_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:12.596284+00:00
-- url     : https://prove2.me/submissions/0aaffc6f-9b02-4647-943d-131b0dbf66d4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScalingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegersStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedeanStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeCosetScaledRiemannSum
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_LatSum_card_reps
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_LatSum_tile_pi
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_LatSum_scal_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_isLocR_Ainf
import Theorems.Thm_GlobalTheory_T_archimedean_fundamental_domain_integers
import Theorems.Thm_GlobalTheory_T_lattice_point_count_scaling
import Theorems.Thm_GlobalTheory_T_scaling_measure_product_archimedean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.Equi.LatSum.scal_apply

set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory.CompanionTheory.Equi.LatSum
namespace GlobalTheory.CompanionTheory.Equi
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), IsStdInf li → ∀ (ι : Type) [Fintype ι] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun x : latCoset I x0 => φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) ∧ Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : latCoset I x0, φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ * ∫ y, φ y ∂(Measure.pi fun _ => li))) := by
  intro F _ _ hF θ hθ li hli ι _ I hI x0 φ hφ hφs
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : li.IsAddHaarMeasure := hli.1
  obtain ⟨D₀, K₀, hDm, hK, hDK, hD1, htile⟩ := GlobalTheory.T.archimedean_fundamental_domain_integers F hF li hli
  have hg : Function.Injective (algebraMap F (Ainf F)) := (algebraMap F (Ainf F)).injective
  let j : 𝓞 F →+ Ainf F := ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom
  have hj : Function.Injective j := hg.comp (IsFractionRing.injective (𝓞 F) F)
  let H : AddSubgroup (𝓞 F) := I.toAddSubgroup
  haveI hfin : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  let rep : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv Ideal.Quotient.mk_surjective
  have hrep : ∀ c, Ideal.Quotient.mk I (rep c) = c := Function.surjInv_eq _
  have hq : ∀ a b, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ a - b ∈ H := fun a b => Ideal.Quotient.eq
  let Λ : AddSubgroup (ι → Ainf F) := AddSubgroup.pi Set.univ (fun _ : ι => H.map j)
  haveI : Countable (𝓞 F) := (RingOfIntegers.basis F).equivFun.toEquiv.injective.countable
  haveI : Countable (H.map j) := by
    have : (↑(H.map j) : Set (Ainf F)).Countable := (Set.to_countable (H : Set (𝓞 F))).image j
    exact this.to_subtype
  haveI : Countable Λ := by
    refine Function.Injective.countable (f := fun (l : Λ) (i : ι) => (⟨l.1 i, l.2 i (Set.mem_univ i)⟩ : H.map j)) ?_
    intro l l' h
    exact Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  have hcard : ((reps (ι := ι) j rep).card : ℝ) = (Ideal.absNorm I : ℝ) ^ Fintype.card ι := by
    rw [card_reps j hj (Ideal.Quotient.mk I) rep hrep, Nat.cast_pow, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  let T : ℝ → (ι → Ainf F) →+ (ι → Ainf F) := fun ε => scal ι (θ ε)
  have hjoint : Continuous fun p : ℝ × (ι → Ainf F) => T p.1 p.2 :=
    continuous_pi fun i => (hθ.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have hθ0 : θ 0 = 0 := map_zero θ
  have key := GlobalTheory.T.lattice_point_count_scaling (ι → Ainf F) (Measure.pi fun _ => li) Λ (Set.pi Set.univ fun _ => D₀)
    (Set.pi Set.univ fun _ => K₀) (reps (ι := ι) j rep) T (Module.finrank ℚ F * Fintype.card ι)
    (MeasurableSet.univ_pi fun _ => hDm) (isCompact_univ_pi fun _ => hK)
    (Set.pi_mono fun _ _ => hDK)
    (by rw [Measure.pi_pi]; simp [hD1])
    (fun y => tile_pi H j hj (Ideal.Quotient.mk I) rep hrep hq D₀ htile y)
    (fun ε _ => continuous_pi fun i => continuous_const.mul (continuous_apply i))
    (fun ε hε y => by
      have h1 : θ ε⁻¹ * θ ε = 1 := by rw [← map_mul, inv_mul_cancel₀ hε.ne', map_one]
      have h2 : θ ε * θ ε⁻¹ = 1 := by rw [mul_comm, h1]
      constructor
      · funext i
        show θ ε⁻¹ * (θ ε * y i) = y i
        rw [← mul_assoc, h1, one_mul]
      · funext i
        show θ ε * (θ ε⁻¹ * y i) = y i
        rw [← mul_assoc, h2, one_mul])
    (fun ε hε => GlobalTheory.T.scaling_measure_product_archimedean F hF θ hθ li hli.1 ι ε hε)
    (fun B hB U hU => by
      have h0 : ∀ b ∈ B, ∀ᶠ z : ℝ × (ι → Ainf F) in 𝓝 ((0 : ℝ), b), T z.1 z.2 ∈ U := by
        intro b _
        refine hjoint.continuousAt.eventually_mem ?_
        have : T (0 : ℝ) b = 0 := by
          funext i
          show θ 0 * b i = 0
          rw [hθ0, zero_mul]
        simpa [this] using hU
      exact (hB.eventually_forall_of_forall_eventually h0).filter_mono nhdsWithin_le_nhds)
    (fun i => algebraMap F (Ainf F) (x0 i)) φ hφ hφs
  rw [hcard] at key

  let f : latCoset I x0 → Λ := fun x => ⟨fun i => algebraMap F (Ainf F) (x.1 i - x0 i), fun i _ => by
    obtain ⟨y, hy, e⟩ := x.2 i
    refine AddSubgroup.mem_map.2 ⟨y, hy, ?_⟩
    show algebraMap F (Ainf F) (y : F) = algebraMap F (Ainf F) (x.1 i - x0 i)
    rw [e]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x x' h
      refine Subtype.ext (funext fun i => ?_)
      have h1 := hg (congrFun (congrArg Subtype.val h) i)
      exact sub_left_injective h1
    · rintro ⟨l, hl⟩
      have hy : ∀ i, ∃ y ∈ I, j y = l i := fun i => by
        obtain ⟨y, hy, e⟩ := AddSubgroup.mem_map.1 (hl i (Set.mem_univ i))
        exact ⟨y, hy, e⟩
      choose y hyI hyl using hy
      refine ⟨⟨fun i => x0 i + (y i : F), fun i => ⟨y i, hyI i, by simp⟩⟩, Subtype.ext (funext fun i => ?_)⟩
      show algebraMap F (Ainf F) (x0 i + (y i : F) - x0 i) = l i
      rw [add_sub_cancel_left, ← hyl]
      rfl
  let e : latCoset I x0 ≃ Λ := Equiv.ofBijective f hf
  have hterm : ∀ (ε : ℝ) (x : latCoset I x0), φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i)) =
      φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + (e x : ι → Ainf F))) := by
    intro ε x
    congr 1
    funext i
    show _ = θ ε * (algebraMap F (Ainf F) (x0 i) + algebraMap F (Ainf F) (x.1 i - x0 i))
    rw [← map_add, add_sub_cancel]
  constructor
  · intro ε hε
    have h1 := (e.summable_iff (f := fun l : Λ => φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + l)))).2 (key.1 ε hε)
    refine h1.congr fun x => ?_
    exact (hterm ε x).symm
  · refine key.2.congr fun ε => ?_
    congr 1
    rw [← e.tsum_eq]
    exact tsum_congr fun x => (hterm ε x).symm
end GlobalTheory.CompanionTheory.Equi
