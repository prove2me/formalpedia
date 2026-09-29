-- Prove2me | solution 1 for LanglandsTunnell.finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5c71f119-29b8-5458-bb57-136f821a8128

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt
set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell UnramifiedWhittaker
open NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws23HeckeLocal

open Matrix MeasureTheory NumberField.InfinitePlace.Completion

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ

abbrev w0 : InfinitePlace ℚ := default
theorem hw0 : (w0).IsReal := IsTotallyReal.isReal _

abbrev eR : (w0).Completion ≃+* ℝ := ringEquivRealOfIsReal hw0

abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hw0

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = w0 := Subsingleton.elim _ _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl := infinitePlace_eq v
  show archMatrixUpdate ℚ w0 ((glEquivOfRingEquiv (eR).symm M : GL (Fin 2) (w0).Completion) : Matrix _ _ _) i j w0 = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem iotaR_snd (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := rfl

abbrev fstM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)

abbrev sndM (g : G2) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)

theorem fstM_mul (g h : G2) : fstM (g * h) = fstM g * fstM h :=
  (RingHom.mapMatrix _).map_mul _ _

theorem sndM_mul (g h : G2) : sndM (g * h) = sndM g * sndM h :=
  (RingHom.mapMatrix _).map_mul _ _

theorem eq_of_fstM_sndM {g h : G2} (h1 : fstM g = fstM h) (h2 : sndM g = sndM h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem fstM_eq_one_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : fstM g = 1 := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) hg

theorem sndM_iotaR (M : GL (Fin 2) ℝ) : sndM (ιR M) = 1 :=
  Matrix.ext fun i j => iotaR_snd M i j

theorem iotaR_mul_comm {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) :
    ιR M * g = g * ιR M := by
  refine eq_of_fstM_sndM ?_ ?_
  · rw [fstM_mul, fstM_mul, fstM_eq_one_of_mem hg, mul_one, one_mul]
  · rw [sndM_mul, sndM_mul, sndM_iotaR, mul_one, one_mul]

abbrev pinsQ (D : Set G2) : CarrierPins ℚ :=
  productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

abbrev Wφ (D : Set G2) (φ : G2 → ℂ) : G2 → ℂ :=
  whittakerCoefficient ℚ (pinsQ D) NumberField.StandardAddChar.psiQ φ 1

theorem Wφ_apply (D : Set G2) (φ : G2 → ℂ) (g : G2) :
    Wφ D φ g = ∫ x, φ (unipotentGL2 x * g) * NumberField.StandardAddChar.psiQ (-x)
      ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  show (∫ x, φ (unipotentGL2 x * g) * NumberField.StandardAddChar.psiQ (-(algebraMap ℚ 𝔸 1 * x))
      ∂(ProbabilityTheory.cond μA (adelicBox ℚ))) = _
  congr 1; funext x; rw [map_one, one_mul]

theorem globalPoints_unipotentGL2 (k : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 k) = unipotentGL2 (algebraMap ℚ 𝔸 k) := by
  refine Units.ext ?_
  change (algebraMap ℚ 𝔸).mapMatrix ((unipotentGL2 k : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
  rw [unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

scoped instance isAddHaarMeasure_adelicAddHaar' : (μA).IsAddHaarMeasure :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

scoped instance countable_principalSubgroup' : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  show Countable {x : 𝔸 // x ∈ Set.range (algebraMap ℚ 𝔸)}
  exact (Set.countable_range _).to_subtype

theorem integral_cond_adelicBox_comp_add_right (P : 𝔸 → ℂ)
    (hP : ∀ (k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸), P ((k : 𝔸) + x) = P x) (a : 𝔸) :
    ∫ x, P (x + a) ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) =
      ∫ x, P x ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  have hcond : ProbabilityTheory.cond μA (adelicBox ℚ) =
      ((μA) (adelicBox ℚ))⁻¹ • (μA).restrict (adelicBox ℚ) := rfl
  rw [hcond, integral_smul_measure, integral_smul_measure]
  congr 1
  rw [← (measurePreserving_add_right (μA) a).setIntegral_image_emb (measurableEmbedding_addRight a) P
    (adelicBox ℚ)]
  have hbox := isAddFundamentalDomain_adelicBox ℚ (μA)
  have himg : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun x : 𝔸 => x + a) '' adelicBox ℚ) μA := by
    refine hbox.image_of_equiv (ν := μA) (Equiv.addRight a)
      (by simpa using (measurePreserving_add_right (μA) (-a)).quasiMeasurePreserving) (Equiv.refl _) ?_
    intro k x
    show (k : 𝔸) + x + a = (k : 𝔸) + (x + a)
    rw [add_assoc]
  exact MeasureTheory.IsAddFundamentalDomain.setIntegral_eq himg hbox (f := P) (fun k x => hP k x)

theorem left_invariant_of_iso {D : Set G2} {ξ : (pinsQ D).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : G2 → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ) (γ : GL (Fin 2) ℚ) (g : G2) :
    φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g := by
  letI := (pinsQ D).mS
  exact ((lsXiMemberAt_iff (𝓞 ℚ) ℚ (pinsQ D).μ (pinsQ D).Z ξ (pinsQ D).D φ).1 hiso.smoothCusp.1.1).1.left_invariant γ g

theorem central_of_iso {D : Set G2} {ξ : (pinsQ D).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : G2 → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ) (z : (pinsQ D).Z) (g : G2) :
    φ (centralScalar (𝓞 ℚ) ℚ (z : (𝔸)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g := by
  letI := (pinsQ D).mS
  exact ((lsXiMemberAt_iff (𝓞 ℚ) ℚ (pinsQ D).μ (pinsQ D).Z ξ (pinsQ D).D φ).1 hiso.smoothCusp.1.1).1.central_transform z g

theorem Wφ_unipotentGL2_mul {D : Set G2} {φ : G2 → ℂ}
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : G2), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g) (b : 𝔸) (g : G2) :
    Wφ D φ (unipotentGL2 b * g) = NumberField.StandardAddChar.psiQ b * Wφ D φ g := by
  set P : 𝔸 → ℂ := fun t => φ (unipotentGL2 t * g) * NumberField.StandardAddChar.psiQ (-t) with hP
  have hPer : ∀ (k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸), P ((k : 𝔸) + x) = P x := by
    rintro ⟨_, k, rfl⟩ x
    simp only [hP]
    rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ, neg_add, AddChar.map_add_eq_mul,
      ← map_neg, NumberField.StandardAddChar.psiQ_algebraMap, one_mul]
  have hshift : ∀ t : 𝔸, φ (unipotentGL2 t * (unipotentGL2 b * g)) * NumberField.StandardAddChar.psiQ (-t) =
      NumberField.StandardAddChar.psiQ b * P (t + b) := by
    intro t
    simp only [hP]
    rw [← mul_assoc, ← unipotentGL2_add, mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [Wφ_apply, Wφ_apply]
  simp_rw [hshift]
  rw [integral_const_mul, integral_cond_adelicBox_comp_add_right P hPer b]

theorem Wφ_mul_right {D : Set G2} {φ : G2 → ℂ} (r : G2) (c : ℂ) (hr : ∀ h : G2, φ (h * r) = c * φ h)
    (g : G2) : Wφ D φ (g * r) = c * Wφ D φ g := by
  rw [Wφ_apply, Wφ_apply, ← integral_const_mul]
  congr 1; funext x
  rw [← mul_assoc, hr, mul_assoc]

theorem centralScalar_comm (u : (𝔸)ˣ) (g : G2) : centralScalar (𝓞 ℚ) ℚ u * g = g * centralScalar (𝓞 ℚ) ℚ u := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (u : 𝔸) * (g : Matrix (Fin 2) (Fin 2) 𝔸) = (g : Matrix (Fin 2) (Fin 2) 𝔸) * Matrix.scalar (Fin 2) (u : 𝔸)
  exact (Matrix.scalar_commute (u : 𝔸) (fun r' => Commute.all _ r') _).eq

theorem ratArchGL2_apply (g : G2) (i j : Fin 2) :
    ((ratArchGL2 g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = eR (((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0) := rfl

theorem ratArchGL2_mul (g h : G2) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, map_mul, map_mul]

theorem ratArchGL2_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

theorem ratArchGL2_iotaR (M : GL (Fin 2) ℝ) : ratArchGL2 (ιR M) = M := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [ratArchGL2_apply, iotaR_fst]
  exact (eR).apply_symm_apply _

theorem coe_finFactor (g : G2) : (RSCarrier.finFactor g : G2) = (ιR (ratArchGL2 g))⁻¹ * g := rfl

theorem finFactor_iotaR_mul (M : GL (Fin 2) ℝ) {x : G2} (hx : x ∈ finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (ιR M * x) = ⟨x, hx⟩ := by
  apply Subtype.ext
  rw [coe_finFactor, ratArchGL2_mul, ratArchGL2_iotaR, ratArchGL2_of_mem hx, mul_one, inv_mul_cancel_left]

theorem finFactor_mul_of_mem (g : G2) {x : G2} (hx : x ∈ finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (g * x) = ⟨(RSCarrier.finFactor g : G2) * x, mul_mem (RSCarrier.finFactor g).2 hx⟩ := by
  apply Subtype.ext
  show (ιR (ratArchGL2 (g * x)))⁻¹ * (g * x) = (ιR (ratArchGL2 g))⁻¹ * g * x
  rw [ratArchGL2_mul, ratArchGL2_of_mem hx, mul_one, mul_assoc]

theorem finFactor_mul_of_mem_left (g : G2) {x : G2} (hx : x ∈ finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (x * g) = ⟨x * (RSCarrier.finFactor g : G2), mul_mem hx (RSCarrier.finFactor g).2⟩ := by
  apply Subtype.ext
  show (ιR (ratArchGL2 (x * g)))⁻¹ * (x * g) = x * ((ιR (ratArchGL2 g))⁻¹ * g)
  rw [ratArchGL2_mul, ratArchGL2_of_mem hx, one_mul, ← mul_assoc, ← mul_assoc, ← map_inv, iotaR_mul_comm hx]

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

abbrev Kp : Type := p.adicCompletion ℚ
abbrev Op : Type := p.adicCompletionIntegers ℚ

theorem placeEmbed_eq (x : GL (Fin 2) (Kp p)) :
    placeEmbed ℚ p x = AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x) := rfl

theorem placeEmbed_mem_fin (x : GL (Fin 2) (Kp p)) : placeEmbed ℚ p x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff, placeEmbed_eq, AdelicDock.glArch_finEmbed]

theorem localAt_placeEmbed (x : GL (Fin 2) (Kp p)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ
    (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

variable {p}

theorem idealBound_eq_one {N : Ideal (𝓞 ℚ)} (hpN : ¬ N ≤ p.asIdeal) : AdelicLevel.idealBound (𝓞 ℚ) N p = 1 := by
  have hN : N ≠ ⊥ := fun h => hpN (h ▸ bot_le)
  exact AdelicLevel.idealBound_eq_one_of_not_dvd hN (fun h => hpN (Ideal.le_of_dvd h))

theorem isLocalLevelOne_of_top {N : Ideal (𝓞 ℚ)} (hpN : ¬ N ≤ p.asIdeal) {m : Matrix (Fin 2) (Fin 2) (Kp p)}
    (hm : AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m) : AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m := by
  refine ⟨hm.integral, ?_, ?_⟩
  · rw [idealBound_eq_one hpN, ← AdelicLevel.idealBound_top (R := 𝓞 ℚ) p]; exact hm.lowerLeft
  · rw [idealBound_eq_one hpN, ← AdelicLevel.idealBound_top (R := 𝓞 ℚ) p]; exact hm.lowerRight

theorem mem_localLevelOne_of_top {N : Ideal (𝓞 ℚ)} (hpN : ¬ N ≤ p.asIdeal) {x : GL (Fin 2) (Kp p)}
    (hx : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
  rw [AdelicDock.mem_localLevelOne_iff] at hx ⊢
  exact ⟨isLocalLevelOne_of_top hpN hx.1, isLocalLevelOne_of_top hpN hx.2⟩

theorem placeEmbed_mem_U {N : Ideal (𝓞 ℚ)} (hpN : ¬ N ≤ p.asIdeal) {x : GL (Fin 2) (Kp p)}
    (hx : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    placeEmbed ℚ p x ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ := by
  refine Subgroup.mem_inf.2 ⟨?_, placeEmbed_mem_fin p x⟩
  rw [placeEmbed_eq, AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff]
  exact mem_localLevelOne_of_top hpN hx

theorem mem_localLevelOne_top_of_entries {x : GL (Fin 2) (Kp p)}
    (h1 : ∀ i j, (x : Matrix (Fin 2) (Fin 2) (Kp p)) i j ∈ p.adicCompletionIntegers ℚ)
    (h2 : ∀ i j, ((x⁻¹ : GL (Fin 2) (Kp p)) : Matrix (Fin 2) (Fin 2) (Kp p)) i j ∈ p.adicCompletionIntegers ℚ) :
    x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (Kp p), (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨hm, ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0)
    · rw [AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (hm 1 1) (one_mem _))
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨key _ h1, key _ h2⟩

theorem mem_localLevelOne_top_of_mem_integralSubgroup {x : GL (Fin 2) (Kp p)}
    (hx : x ∈ LocalGL2.integralSubgroup (Op p) (Kp p)) : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  refine mem_localLevelOne_top_of_entries (fun i j => ?_) (fun i j => ?_)
  · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hx i j
    rw [← hr]; exact r.2
  · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup (inv_mem hx) i j
    rw [← hr]; exact r.2

theorem localAt_mem_integralSubgroup {N : Ideal (𝓞 ℚ)} {u : G2}
    (hu : u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) :
    localAt ℚ p u ∈ LocalGL2.integralSubgroup (Op p) (Kp p) := by
  have h := (AdelicLevel.mem_levelOne_iff.1 hu.1)
  rw [AdelicLevel.mem_finiteLevelOne_iff] at h
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem (IsFractionRing.injective (Op p) (Kp p))]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have hij := h.1.integral i j p
    exact ⟨⟨_, hij⟩, rfl⟩
  · exact ⟨⟨_, h.2.integral i j p⟩, rfl⟩

end Place

section PlaceTwo

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem heckeGenAt_eq_placeEmbed (t : (Kp p)ˣ) :
    heckeGenAt (𝓞 ℚ) ℚ p t = placeEmbed ℚ p (diagOne t) := by
  refine Units.ext (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_)
  · rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_arch_finMat]
    ext i j
    exact heckeGenAt_fst t i j
  · rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = p
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      ext i j : 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, AdelicLevel.adeleFin_apply, heckeGenAt_snd_apply_self, diagOne_coe_apply]
    · rw [AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hw]
      ext i j : 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, AdelicLevel.adeleFin_apply, heckeGenAt_snd_apply_of_ne t hw]

theorem scalar_val_apply (w : (Kp p)ˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) w : GL (Fin 2) (Kp p)) : Matrix (Fin 2) (Fin 2) (Kp p)) i j =
      if i = j then (w : Kp p) else 0 := rfl

theorem centralScalar_val_apply (u : (𝔸)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 ℚ) ℚ u : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j = if i = j then (u : 𝔸) else 0 := rfl

theorem finIncl_fst (x : FiniteAdeleRing (𝓞 ℚ) ℚ) : (AdelicLevel.finIncl (𝓞 ℚ) ℚ x).1 = 1 := rfl
theorem finIncl_snd (x : FiniteAdeleRing (𝓞 ℚ) ℚ) : (AdelicLevel.finIncl (𝓞 ℚ) ℚ x).2 = x := rfl

theorem centralScalar_eq_placeEmbed (t : (Kp p)ˣ) :
    centralScalar (𝓞 ℚ) ℚ (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ p t)) =
      placeEmbed ℚ p (Matrix.GeneralLinearGroup.scalar (Fin 2) t) := by
  refine Units.ext (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_)
  · rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_arch_finMat]
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply, centralScalar_val_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, Matrix.one_apply_eq, Units.coe_map, finIncl_fst]
    · rw [if_neg hij, Matrix.one_apply_ne hij]
      rfl
  · rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = p
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      ext i j : 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, AdelicLevel.adeleFin_apply, centralScalar_val_apply, scalar_val_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij, Units.coe_map, finIncl_snd, AdelicLevel.localUnit_apply_self]
      · rw [if_neg hij, if_neg hij]
        rfl
    · rw [AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hw]
      ext i j : 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, AdelicLevel.adeleFin_apply, centralScalar_val_apply]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, Matrix.one_apply_eq, Units.coe_map, finIncl_snd,
          AdelicLevel.localUnit_apply_of_ne _ _ _ _ hw]
      · rw [if_neg hij, Matrix.one_apply_ne hij]
        rfl

theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(a : A), 1]).det = a
  rw [Matrix.det_diagonal]; simp

theorem det_heckeGenAt (t : (Kp p)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 ℚ) ℚ p t) =
      Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ p t) :=
  det_diagOne _

theorem centralScalar_det_heckeGen :
    centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ p)) =
      placeEmbed ℚ p (Matrix.GeneralLinearGroup.scalar (Fin 2) (AdelicLevel.uniformizerUnit ℚ p)) := by
  show centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 ℚ) ℚ p _)) = _
  rw [det_heckeGenAt, centralScalar_eq_placeEmbed]

variable {p}

theorem repSome_eq (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0) (b : Op p) :
    repSome (algebraMap (Op p) (Kp p) ϖ) hπ (algebraMap (Op p) (Kp p) b) = LocalGL2.localRepSome ϖ hπ b :=
  Units.ext (by rw [LocalGL2.coe_localRepSome]; rfl)

theorem repInf_eq (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0) :
    repInf (algebraMap (Op p) (Kp p) ϖ) hπ = LocalGL2.localRepInf ϖ hπ :=
  Units.ext (by rw [LocalGL2.coe_localRepInf]; rfl)

theorem diagPi_eq (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0) :
    LocalGL2.diagPi ϖ hπ = diagOne (Units.mk0 _ hπ) := by
  refine Units.ext ?_
  rw [LocalGL2.coe_diagPi]
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem scalarPi_eq (π : Kp p) (hπ : π ≠ 0) :
    scalarPi π hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 π hπ) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPi, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem valued_le_one_of_eq_one {u : (Kp p)ˣ} (hu : Valued.v (u : Kp p) = 1) :
    (u : Kp p) ∈ p.adicCompletionIntegers ℚ ∧ ((u⁻¹ : (Kp p)ˣ) : Kp p) ∈ p.adicCompletionIntegers ℚ := by
  refine ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le,
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem scalar_mem_localLevelOne_top {u : (Kp p)ˣ} (hu : Valued.v (u : Kp p) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  obtain ⟨h1, h2⟩ := valued_le_one_of_eq_one hu
  refine mem_localLevelOne_top_of_entries (fun i j => ?_) (fun i j => ?_)
  · rw [scalar_val_apply]
    split_ifs
    · exact h1
    · exact zero_mem (p.adicCompletionIntegers ℚ)
  · rw [← map_inv, scalar_val_apply]
    split_ifs
    · exact h2
    · exact zero_mem (p.adicCompletionIntegers ℚ)

theorem diagOne_mem_localLevelOne_top {u : (Kp p)ˣ} (hu : Valued.v (u : Kp p) = 1) :
    diagOne u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  obtain ⟨h1, h2⟩ := valued_le_one_of_eq_one hu
  have key : ∀ w : (Kp p)ˣ, (w : Kp p) ∈ p.adicCompletionIntegers ℚ →
      ∀ i j, ((diagOne w : GL (Fin 2) (Kp p)) : Matrix (Fin 2) (Fin 2) (Kp p)) i j ∈ p.adicCompletionIntegers ℚ := by
    intro w hw i j
    rw [diagOne_coe_apply]
    fin_cases i <;> fin_cases j
    · exact hw
    · exact zero_mem (p.adicCompletionIntegers ℚ)
    · exact zero_mem (p.adicCompletionIntegers ℚ)
    · exact one_mem (p.adicCompletionIntegers ℚ)
  refine mem_localLevelOne_top_of_entries (key u h1) (fun i j => ?_)
  rw [← map_inv]
  exact key u⁻¹ h2 i j

end PlaceTwo

section Reps

variable {p : HeightOneSpectrum (𝓞 ℚ)} {N : Ideal (𝓞 ℚ)}

abbrev bq (p : HeightOneSpectrum (𝓞 ℚ)) (i : 𝓞 ℚ ⧸ p.asIdeal) : Op p :=
  algebraMap (𝓞 ℚ) (Op p) (Quotient.out i)

def reps' (p : HeightOneSpectrum (𝓞 ℚ)) (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (o : Option (𝓞 ℚ ⧸ p.asIdeal)) : G2 :=
  o.elim (placeEmbed ℚ p (LocalGL2.localRepInf ϖ hπ)) (fun i => placeEmbed ℚ p (LocalGL2.localRepSome ϖ hπ (bq p i)))

theorem reps'_mem_fin (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0) (o : Option (𝓞 ℚ ⧸ p.asIdeal)) :
    reps' p ϖ hπ o ∈ finiteAdelicGL2Subgroup ℚ := by
  cases o with
  | none => exact placeEmbed_mem_fin p _
  | some i => exact placeEmbed_mem_fin p _

theorem valued_ϖ_lt_one {ϖ : Op p} (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ)) :
    Valued.v (algebraMap (Op p) (Kp p) ϖ) < 1 := by
  rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem not_isUnit_ϖ {ϖ : Op p} (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ)) :
    ¬ IsUnit ϖ := by
  rintro ⟨w, rfl⟩
  have h1 : Valued.v (algebraMap (Op p) (Kp p) (w : Op p)) *
      Valued.v (algebraMap (Op p) (Kp p) ((w⁻¹ : (Op p)ˣ) : Op p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hle : Valued.v (algebraMap (Op p) (Kp p) ((w⁻¹ : (Op p)ˣ) : Op p)) ≤ 1 := ((w⁻¹ : (Op p)ˣ) : Op p).2
  have := mul_lt_one_of_lt_of_le (valued_ϖ_lt_one hϖ) hle
  rw [h1] at this
  exact lt_irrefl _ this

theorem heckeGenAt_mk0_eq (N : Ideal (𝓞 ℚ)) (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ u₀ ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ,
      placeEmbed ℚ p (LocalGL2.diagPi ϖ hπ) = heckeGen (𝓞 ℚ) ℚ p * u₀ := by
  set tϖ : (Kp p)ˣ := Units.mk0 (algebraMap (Op p) (Kp p) ϖ) hπ with htϖ
  have htv : Valued.v (tϖ : Kp p) = WithZero.exp (-1 : ℤ) := hϖ
  refine ⟨(heckeGen (𝓞 ℚ) ℚ p)⁻¹ * heckeGenAt (𝓞 ℚ) ℚ p tϖ, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · exact heckeGen_inv_mul_heckeGenAt_mem_levelOne tϖ htv N
  · have h1 : heckeGenAt (𝓞 ℚ) ℚ p tϖ ∈ finiteAdelicGL2Subgroup ℚ := by
      rw [heckeGenAt_eq_placeEmbed]; exact placeEmbed_mem_fin p _
    have h2 : heckeGen (𝓞 ℚ) ℚ p ∈ finiteAdelicGL2Subgroup ℚ := by
      show heckeGenAt (𝓞 ℚ) ℚ p _ ∈ _
      rw [heckeGenAt_eq_placeEmbed]; exact placeEmbed_mem_fin p _
    exact mul_mem (inv_mem h2) h1
  · rw [mul_inv_cancel_left, diagPi_eq, ← heckeGenAt_eq_placeEmbed]

theorem placeEmbed_integral_mem_U (hpN : ¬ N ≤ p.asIdeal) {x : GL (Fin 2) (Kp p)}
    (hx : x ∈ LocalGL2.integralSubgroup (Op p) (Kp p)) :
    placeEmbed ℚ p x ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ :=
  placeEmbed_mem_U hpN (mem_localLevelOne_top_of_mem_integralSubgroup hx)

theorem reps'_mem_doubleCoset (hpN : ¬ N ≤ p.asIdeal) (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ)) (o : Option (𝓞 ℚ ⧸ p.asIdeal)) :
    reps' p ϖ hπ o ∈ HeckePair.doubleCoset (levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (heckeGen (𝓞 ℚ) ℚ p) := by
  obtain ⟨u₀, hu₀, hgen⟩ := heckeGenAt_mk0_eq N ϖ hπ hϖ
  cases o with
  | none =>
    show placeEmbed ℚ p (LocalGL2.weylInt (Op p) (Kp p) * LocalGL2.diagPi ϖ hπ * LocalGL2.weylInt (Op p) (Kp p)) ∈ _
    rw [map_mul, map_mul, hgen]
    refine HeckePair.mem_doubleCoset_iff.2 ⟨_, placeEmbed_integral_mem_U hpN LocalGL2.weylInt_mem, _,
      mul_mem hu₀ (placeEmbed_integral_mem_U hpN LocalGL2.weylInt_mem), by simp only [mul_assoc]⟩
  | some i =>
    show placeEmbed ℚ p (LocalGL2.unipotentInt (Kp p) (bq p i) * LocalGL2.diagPi ϖ hπ) ∈ _
    rw [map_mul, hgen]
    exact HeckePair.mem_doubleCoset_iff.2 ⟨_, placeEmbed_integral_mem_U hpN (LocalGL2.unipotentInt_mem (bq p i)), _,
      hu₀, by simp only [mul_assoc]⟩

theorem mem_asIdeal_of_dvd {ϖ : Op p} (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ))
    {r : 𝓞 ℚ} (h : ϖ ∣ algebraMap (𝓞 ℚ) (Op p) r) : r ∈ p.asIdeal := by
  obtain ⟨c, hc⟩ := h
  have hv : Valued.v ((algebraMap (𝓞 ℚ) (Op p) r : Kp p)) < 1 := by
    rw [hc, Subring.coe_mul, map_mul]
    have hc1 : Valued.v (c : Kp p) ≤ 1 := c.2
    exact mul_lt_one_of_lt_of_le (valued_ϖ_lt_one hϖ) hc1
  have : Valued.v ((algebraMap (𝓞 ℚ) (Op p) r : Kp p)) = p.intValuation r := AdelicBox.valued_algebraMap (𝓞 ℚ) ℚ p r
  rw [this] at hv
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).1 hv

theorem reps'_mk_injective (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ)) :
    Function.Injective fun o => (QuotientGroup.mk (reps' p ϖ hπ o) :
      G2 ⧸ (levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)) := by
  intro o o' h
  have hloc : (QuotientGroup.mk (localAt ℚ p (reps' p ϖ hπ o)) : GL (Fin 2) (Kp p) ⧸ LocalGL2.integralSubgroup (Op p) (Kp p)) =
      QuotientGroup.mk (localAt ℚ p (reps' p ϖ hπ o')) := by
    simp only at h
    rw [QuotientGroup.eq] at h ⊢
    rw [← map_inv, ← map_mul]
    exact localAt_mem_integralSubgroup h
  have hunit := not_isUnit_ϖ hϖ
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some i' =>
      exfalso
      simp only [reps', Option.elim, localAt_placeEmbed] at hloc
      exact LocalGL2.mk_localRepSome_ne_mk_localRepInf ϖ hπ hunit _ hloc.symm
  | some i =>
    cases o' with
    | none =>
      exfalso
      simp only [reps', Option.elim, localAt_placeEmbed] at hloc
      exact LocalGL2.mk_localRepSome_ne_mk_localRepInf ϖ hπ hunit _ hloc
    | some i' =>
      simp only [reps', Option.elim, localAt_placeEmbed] at hloc
      have hdvd := LocalGL2.dvd_sub_of_mk_localRepSome_eq ϖ hπ hloc
      rw [← map_sub] at hdvd
      have hmem := mem_asIdeal_of_dvd hϖ hdvd
      congr 1
      rw [← Quotient.out_eq i, ← Quotient.out_eq i']
      exact (Ideal.Quotient.eq.2 hmem).symm

theorem card_option_quot [Fintype (𝓞 ℚ ⧸ p.asIdeal)] :
    Fintype.card (Option (𝓞 ℚ ⧸ p.asIdeal)) = Ideal.absNorm p.asIdeal + 1 := by
  rw [Fintype.card_option, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end Reps

section PhiLevel

variable {D : Set G2} {ξ : (pinsQ D).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  {Φ : HeckeEigensystem ℚ ℂ} {φ : G2 → ℂ} {p : HeightOneSpectrum (𝓞 ℚ)}

theorem hecke_phi (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ) [Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (hpS : p ∉ S) (hpN : ¬ N ≤ p.asIdeal) (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ)) (h : G2) :
    ∑ o : Option (𝓞 ℚ ⧸ p.asIdeal), φ (h * reps' p ϖ hπ o) = Φ.a p * φ h := by
  obtain ⟨reps, hsys, hsum⟩ := hiso.hecke_eigen p hpS
  have hcov : ∀ o : Option (𝓞 ℚ ⧸ p.asIdeal), ∃ i,
      (QuotientGroup.mk (reps' p ϖ hπ o) : G2 ⧸ (levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)) =
        QuotientGroup.mk (reps i) :=
    fun o => hsys.covers _ (reps'_mem_doubleCoset hpN ϖ hπ hϖ o)
  choose σ hσ using hcov
  have hσinj : Function.Injective σ := by
    intro o o' hoo
    apply reps'_mk_injective (N := N) ϖ hπ hϖ
    simp only [hσ, hoo]
  have hcard : Fintype.card (Option (𝓞 ℚ ⧸ p.asIdeal)) = Fintype.card (Fin (Ideal.absNorm p.asIdeal + 1)) := by
    rw [card_option_quot, Fintype.card_fin]
  have hbij : Function.Bijective σ := (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσinj, hcard⟩
  have hs := hsum h
  unfold SmoothCusp.heckeCosetSum at hs
  rw [← hs, ← Equiv.sum_comp (Equiv.ofBijective σ hbij)]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hu : (reps' p ϖ hπ o)⁻¹ * reps (σ o) ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ :=
    QuotientGroup.eq.1 (hσ o)
  rw [Equiv.ofBijective_apply, ← hiso.level_invariant (h * reps' p ϖ hπ o) _ hu, mul_assoc, mul_inv_cancel_left]

end PhiLevel

section WLevel

variable {D : Set G2} {ξ : (pinsQ D).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  {Φ : HeckeEigensystem ℚ ℂ} {φ : G2 → ℂ} {p : HeightOneSpectrum (𝓞 ℚ)}

theorem integrable_whittakerIntegrand (hφc : Continuous φ) (g : G2) :
    Integrable (fun x : 𝔸 => φ (unipotentGL2 x * g) * NumberField.StandardAddChar.psiQ (-x))
      (ProbabilityTheory.cond μA (adelicBox ℚ)) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μA (adelicBox ℚ)) := isProbabilityMeasure_cond_adelicBox ℚ
  have hF : Continuous fun x : 𝔸 => φ (unipotentGL2 x * g) * NumberField.StandardAddChar.psiQ (-x) :=
    (hφc.comp ((AutomorphicForm.continuous_unipotentGL2 (R := 𝔸)).mul continuous_const)).mul
      (NumberField.StandardAddChar.continuous_psiQ.comp continuous_neg)
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset ℚ
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.mono' (integrable_const B) hF.aestronglyMeasurable ?_
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := μA) (measurableSet_adelicBox ℚ)] with x hx
  exact hB x (hBC hx)

theorem Wφ_sum_mul_right {ι : Type*} [Fintype ι] (hφc : Continuous φ) (r : ι → G2) (c : ℂ)
    (hr : ∀ h : G2, ∑ i, φ (h * r i) = c * φ h) (g : G2) : ∑ i, Wφ D φ (g * r i) = c * Wφ D φ g := by
  simp only [Wφ_apply]
  rw [← integral_finsetSum _ (fun i _ => integrable_whittakerIntegrand hφc (g * r i)), ← integral_const_mul]
  congr 1; funext x
  rw [← Finset.sum_mul, ← mul_assoc]
  congr 1
  simp_rw [← mul_assoc]
  exact hr _

theorem Wφ_mul_right_inv (r : G2) (hr : ∀ h : G2, φ (h * r) = φ h) (g : G2) : Wφ D φ (g * r) = Wφ D φ g := by
  rw [Wφ_mul_right r 1 (fun h => by rw [hr, one_mul]) g, one_mul]

theorem W_levelOne (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ) (hpN : ¬ N ≤ p.asIdeal)
    {x : GL (Fin 2) (Kp p)} (hx : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (g : G2) :
    Wφ D φ (g * placeEmbed ℚ p x) = Wφ D φ g :=
  Wφ_mul_right_inv _ (fun h => hiso.level_invariant h _ (placeEmbed_mem_U hpN hx)) g

theorem W_hecke (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ) [Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (hpS : p ∉ S) (hpN : ¬ N ≤ p.asIdeal) (ϖ : Op p) (hπ : algebraMap (Op p) (Kp p) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (Op p) (Kp p) ϖ) = WithZero.exp (-1 : ℤ)) (g : G2) :
    ∑ o : Option (𝓞 ℚ ⧸ p.asIdeal), Wφ D φ (g * reps' p ϖ hπ o) = Φ.a p * Wφ D φ g :=
  Wφ_sum_mul_right hiso.continuous _ _ (hecke_phi hiso hpS hpN ϖ hπ hϖ) g

theorem W_centre (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ)
    (hpS : p ∉ S) (hpN : ¬ N ≤ p.asIdeal) (π : Kp p) (hπ : π ≠ 0)
    (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (g : G2) :
    Wφ D φ (g * placeEmbed ℚ p (scalarPi π hπ)) = (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wφ D φ g := by

  set w : (Kp p)ˣ := (AdelicLevel.uniformizerUnit ℚ p)⁻¹ * Units.mk0 π hπ with hw
  have hwv : Valued.v (w : Kp p) = 1 := by
    rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, AdelicLevel.valued_uniformizerUnit,
      Units.val_mk0, hϖ, inv_mul_cancel₀ WithZero.exp_ne_zero]
  have hsplit : Units.mk0 π hπ = AdelicLevel.uniformizerUnit ℚ p * w := by rw [hw, mul_inv_cancel_left]
  rw [scalarPi_eq, hsplit, map_mul, map_mul, ← centralScalar_det_heckeGen, ← mul_assoc,
    Wφ_mul_right_inv _ (fun h => hiso.level_invariant h _ (placeEmbed_mem_U hpN (scalar_mem_localLevelOne_top hwv))),
    ← centralScalar_comm]

  have hce := hiso.central_eigen p hpS
  rw [centralScalar_comm]
  rw [Wφ_mul_right _ (Φ.toRawCentral.b p) (fun h => by rw [← centralScalar_comm]; exact hce h) g]
  congr 1
  show (AutomorphicForm.HeckeEigensystem.cNorm p)⁻¹ * Φ.b p = _
  rw [div_eq_inv_mul]
  rfl

def yad (p : HeightOneSpectrum (𝓞 ℚ)) (x : Kp p) : 𝔸 := ((0 : InfiniteAdeleRing ℚ), AdelicDock.splice (𝓞 ℚ) ℚ p 0 x)

theorem placeEmbed_unipotent (x : Kp p) : placeEmbed ℚ p (unipotent x) = unipotentGL2 (yad p x) := by
  refine Units.ext (AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_)
  · rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_arch_finMat, unipotentGL2_coe]
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]
    fin_cases i <;> fin_cases j <;> rfl
  · rw [placeEmbed_eq, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat, AdelicDock.coe_localEmbed, unipotentGL2_coe]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = p
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      ext i j : 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, AdelicLevel.adeleFin_apply]
      fin_cases i <;> fin_cases j
      · rfl
      · show x = (AdelicDock.splice (𝓞 ℚ) ℚ w 0 x) w
        rw [AdelicDock.splice_apply_self]
      · rfl
      · rfl
    · rw [AdelicDock.mapMatrix_localMat_of_ne _ _ _ _ hw]
      ext i j : 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, AdelicLevel.adeleFin_apply]
      fin_cases i <;> fin_cases j
      · rfl
      · show (0 : w.adicCompletion ℚ) = (AdelicDock.splice (𝓞 ℚ) ℚ p 0 x) w
        rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hw]; rfl
      · rfl
      · rfl

theorem psiQ_yad (x : Kp p) : NumberField.StandardAddChar.psiQ (yad p x) = NumberField.StandardAddChar.psiV p x := by
  rw [NumberField.StandardAddChar.psiQ_apply]
  have h1 : (yad p x).1 = 0 := rfl
  rw [h1, AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply]
  rw [finprod_eq_single (fun v => NumberField.StandardAddChar.psiV v ((yad p x).2 v)) p]
  · show NumberField.StandardAddChar.psiV p ((AdelicDock.splice (𝓞 ℚ) ℚ p 0 x) p) = _
    rw [AdelicDock.splice_apply_self]
  · intro v hv
    show NumberField.StandardAddChar.psiV v ((AdelicDock.splice (𝓞 ℚ) ℚ p 0 x) v) = 1
    rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hv]
    exact AddChar.map_zero_eq_one _

theorem W_unipotent (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ) (x : Kp p) (g : G2) :
    Wφ D φ (placeEmbed ℚ p (unipotent x) * g) = NumberField.StandardAddChar.psiV p x * Wφ D φ g := by
  rw [placeEmbed_unipotent, Wφ_unipotentGL2_mul (left_invariant_of_iso hiso), psiQ_yad]

end WLevel

end Ws23HeckeLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt.Ws23HeckeLocal"

open Ws23HeckeLocal in

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hiso : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ N S Φ φ)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (_hfact : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ
          (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
            (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ 1 g
        = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g))
    (_hW : whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ 1 ≠ 0)
    (p : HeightOneSpectrum (𝓞 ℚ)) [Fintype (𝓞 ℚ ⧸ p.asIdeal)] (_hpS : p ∉ S) (_hpN : ¬ N ≤ p.asIdeal)
    (ϖ : p.adicCompletionIntegers ℚ)
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (_hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    (∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wf (RSCarrier.finFactor (placeEmbed ℚ p (unipotent x) * g)) =
        NumberField.StandardAddChar.psiV p x * Wf (RSCarrier.finFactor g)) ∧
    (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
        Wf (RSCarrier.finFactor (g * placeEmbed ℚ p x)) = Wf (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ i : 𝓞 ℚ ⧸ p.asIdeal, Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repSome
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
            (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out i))))))) +
        Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (repInf
          (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        Φ.a p * Wf (RSCarrier.finFactor g)) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor (g * placeEmbed ℚ p (scalarPi
        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ))) =
        (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf (RSCarrier.finFactor g)) := by

  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.1 _hW
  have hWA : WA (ratArchGL2 g₁) ≠ 0 := by
    intro h0; apply hg₁
    show Wφ D φ g₁ = 0
    rw [show Wφ D φ g₁ = WA (ratArchGL2 g₁) * Wf (RSCarrier.finFactor g₁) from _hfact g₁, h0, zero_mul]
  have key : ∀ {x : G2} (hx : x ∈ finiteAdelicGL2Subgroup ℚ),
      Wf ⟨x, hx⟩ = (WA (ratArchGL2 g₁))⁻¹ * Wφ D φ (ιR (ratArchGL2 g₁) * x) := by
    intro x hx
    rw [show Wφ D φ (ιR (ratArchGL2 g₁) * x) = WA (ratArchGL2 (ιR (ratArchGL2 g₁) * x)) *
      Wf (RSCarrier.finFactor (ιR (ratArchGL2 g₁) * x)) from _hfact _, ratArchGL2_mul, ratArchGL2_iotaR,
      ratArchGL2_of_mem hx, mul_one, finFactor_iotaR_mul, inv_mul_cancel_left₀ hWA]
  have keyF : ∀ g : G2, Wf (RSCarrier.finFactor g) =
      (WA (ratArchGL2 g₁))⁻¹ * Wφ D φ (ιR (ratArchGL2 g₁) * (RSCarrier.finFactor g : G2)) :=
    fun g => key (RSCarrier.finFactor g).2
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x g
    rw [finFactor_mul_of_mem_left g (placeEmbed_mem_fin p _), key, keyF g, ← mul_assoc (ιR _),
      iotaR_mul_comm (placeEmbed_mem_fin p _), mul_assoc, W_unipotent _hiso, mul_left_comm]
  ·
    intro x g hx
    rw [finFactor_mul_of_mem g (placeEmbed_mem_fin p _), key, keyF g, ← mul_assoc, W_levelOne _hiso _hpN hx]
  ·
    intro g
    have hsum := W_hecke (D := D) _hiso _hpS _hpN ϖ hπ _hϖ (ιR (ratArchGL2 g₁) * (RSCarrier.finFactor g : G2))
    rw [Fintype.sum_option] at hsum
    simp only [reps', Option.elim] at hsum
    have e1 : ∀ o : G2, o ∈ finiteAdelicGL2Subgroup ℚ →
        Wf (RSCarrier.finFactor (g * o)) = (WA (ratArchGL2 g₁))⁻¹ * Wφ D φ (ιR (ratArchGL2 g₁) * (RSCarrier.finFactor g : G2) * o) := by
      intro o ho
      rw [finFactor_mul_of_mem g ho, key, mul_assoc]
    simp_rw [repSome_eq, repInf_eq]
    rw [keyF g]
    simp_rw [e1 _ (placeEmbed_mem_fin p _)]
    rw [← Finset.mul_sum, ← mul_add, add_comm, hsum, mul_left_comm]
  ·
    intro g
    rw [finFactor_mul_of_mem g (placeEmbed_mem_fin p _), key, keyF g, ← mul_assoc,
      W_centre _hiso _hpS _hpN _ hπ _hϖ, mul_left_comm]

end
p2m_reactivate "P2MW.S_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt.Ws23HeckeLocal"

end S_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt
end P2MW
export P2MW.S_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt (solution)
