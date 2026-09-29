-- Prove2me | solution 1 for LanglandsTunnell.exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/86783113-7d23-5a8e-b012-a246ee32a15c

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_RSCarrierSplit

import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws23FactPhi

open Matrix MeasureTheory NumberField.TateGlobal

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

def aR (x : ℝ) : 𝔸 := (fun v => (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm x, 0)

theorem iotaR_unipotentGL2 (x : ℝ) : ιR (unipotentGL2 x) = unipotentGL2 (aR x) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun v => ?_) ?_)
  · rw [iotaR_fst]
    show _ = ((!![(1 : 𝔸), aR x; 0, 1] i j).1) v
    fin_cases i <;> fin_cases j <;> simp [aR] <;> rfl
  · rw [iotaR_snd]
    show _ = ((!![(1 : 𝔸), aR x; 0, 1] i j).2)
    fin_cases i <;> fin_cases j <;> simp [aR] <;> rfl

abbrev uR (z : ℝˣ) : (𝔸)ˣ :=
  archUnitHom w0 (Units.map (ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm.toMonoidHom z)

theorem uR_fst (z : ℝˣ) (v : InfinitePlace ℚ) :
    ((uR z : (𝔸)ˣ) : 𝔸).1 v = (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (z : ℝ) := by
  obtain rfl := infinitePlace_eq v
  exact NumberField.AdelicVolume.archCentralUnit_fst_self _ _

theorem uR_snd (z : ℝˣ) : ((uR z : (𝔸)ˣ) : 𝔸).2 = 1 := rfl

theorem iotaR_scalar (z : ℝˣ) :
    ιR (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = centralScalar (𝓞 ℚ) ℚ (uR z) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun v => ?_) ?_)
  · rw [iotaR_fst]
    show _ = ((Matrix.scalar (Fin 2) ((uR z : (𝔸)ˣ) : 𝔸) i j).1) v
    fin_cases i <;> fin_cases j <;> simp [uR_fst] <;> rfl
  · rw [iotaR_snd]
    show _ = ((Matrix.scalar (Fin 2) ((uR z : (𝔸)ˣ) : 𝔸) i j).2)
    fin_cases i <;> fin_cases j <;> simp [uR_snd] <;> rfl

theorem iotaR_diagOne (t : ℝˣ) : ιR (diagOne t) = diagOne (uR t) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun v => ?_) ?_)
  · rw [iotaR_fst, diagOne_coe_apply, diagOne_coe_apply]
    show _ = ((Matrix.diagonal ![((uR t : (𝔸)ˣ) : 𝔸), 1] i j).1) v
    fin_cases i <;> fin_cases j <;> simp [uR_fst] <;> rfl
  · rw [iotaR_snd, diagOne_coe_apply]
    show _ = ((Matrix.diagonal ![((uR t : (𝔸)ˣ) : 𝔸), 1] i j).2)
    fin_cases i <;> fin_cases j <;> simp [uR_snd] <;> rfl

def kR (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) : rowIsometrySubgroup₀ (w0).Completion :=
  ⟨glEquivOfRingEquiv (eR).symm κ,
    map_mem_rowIsometrySubgroup₀_of_normPreserving (eR).symm
      (fun x => by rw [← norm_ringEquivRealOfIsReal hw0 ((eR).symm x), RingEquiv.apply_symm_apply]) κ hκ⟩

theorem iotaR_eq_adelicArchGLInclAt (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) :
    ιR κ = adelicArchGLInclAt ℚ w0 ((kR κ hκ : rowIsometrySubgroup₀ (w0).Completion) : GL (Fin 2) (w0).Completion) :=
  rfl

theorem archWeightCharAt_kR (n : ℤ) (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) :
    archWeightCharAt hw0 n (kR κ hκ) = archWeightCharℝ n ⟨κ, hκ⟩ := by
  have hmap : rowIsometrySubgroup₀Map (eR) (norm_ringEquivRealOfIsReal hw0) (kR κ hκ) = ⟨κ, hκ⟩ := by
    apply Subtype.ext
    refine Units.ext (Matrix.ext fun i j => ?_)
    show ((glEquivOfRingEquiv eR (glEquivOfRingEquiv (eR).symm κ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
    rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.apply_symm_apply]
  simp only [archWeightCharAt, archWeightOneAt, archWeightCharℝ, MonoidHom.comp_apply, hmap]

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

theorem Wφ_centralScalar_mul {D : Set G2} {ξ : (pinsQ D).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Φ : HeckeEigensystem ℚ ℂ} {φ : G2 → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ) (u : (𝔸)ˣ) (g : G2) :
    Wφ D φ (centralScalar (𝓞 ℚ) ℚ u * g) =
      ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom u : ℂˣ) : ℂ) * Wφ D φ g := by
  rw [centralScalar_comm]
  refine Wφ_mul_right _ _ (fun h => ?_) g
  rw [← centralScalar_comm]
  exact central_of_iso hiso ⟨u, Subgroup.mem_top u⟩ h

theorem Wφ_mul_iotaR_kappa {D : Set G2} {φ : G2 → ℂ} {k : InfinitePlace ℚ → ℤ}
    (harch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : G2) :
    Wφ D φ (g * ιR κ) = (archWeightCharℝ (k default) ⟨κ, hκ⟩ : ℂ) * Wφ D φ g := by
  refine Wφ_mul_right _ _ (fun h => ?_) g
  rw [iotaR_eq_adelicArchGLInclAt κ hκ, harch w0 hw0 (kR κ hκ) h, archWeightCharAt_kR]

theorem Wφ_iotaR_diagOne_mul {D : Set G2} {φ : G2 → ℂ} {Wr : InfinitePlace ℚ → ℂ → ℂ}
    {C : FiniteAdeleRing (𝓞 ℚ) ℚ → G2 → ℂ}
    (hφW : ∀ a : (𝔸)ˣ, ∀ g : G2, g ∈ finiteAdelicGL2Subgroup ℚ →
      Wφ D φ (diagOne a * g)
        = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : 𝔸).1 w))) * C (a : 𝔸).2 g)
    (t : ℝˣ) {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) :
    Wφ D φ (ιR (diagOne t) * g) = Wr default (t : ℝ) * C 1 g := by
  rw [iotaR_diagOne, hφW (uR t) g hg, uR_snd]
  congr 1
  rw [Fintype.prod_subsingleton _ w0, uR_fst]
  congr 1
  show extensionEmbedding w0 ((eR).symm (t : ℝ)) = ((t : ℝ) : ℂ)
  have h1 : extensionEmbedding w0 ((eR).symm (t : ℝ)) = ((extensionEmbeddingOfIsReal hw0 ((eR).symm (t : ℝ)) : ℝ) : ℂ) :=
    (extensionEmbeddingOfIsReal_apply hw0 _).symm
  rw [h1]
  congr 1
  exact (eR).apply_symm_apply (t : ℝ)

theorem psiQ_aR (x : ℝ) :
    NumberField.StandardAddChar.psiQ (aR x) = Complex.exp (2 * Real.pi * Complex.I * x) := by
  rw [NumberField.StandardAddChar.psiQ_apply]
  have h2 : (aR x).2 = 0 := rfl
  rw [h2, AddChar.map_zero_eq_one, mul_one, NumberField.StandardAddChar.psiArch_apply, finprod_unique,
    NumberField.StandardAddChar.psiArchPlace_apply]
  congr 2
  show ((ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))
    ((ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm x) : ℝ) : ℂ) = x
  rw [RingEquiv.apply_symm_apply]

theorem rot_mem (p q : ℝ) (hpq : p ^ 2 + q ^ 2 = 1) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![p, q; -q, p]
        (by rw [Matrix.det_fin_two_of]; nlinarith) ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  have hdet : (!![p, q; -q, p] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of]; nlinarith
  refine ⟨hdet, ?_, ?_⟩
  · show ‖(!![p, q; -q, p] : Matrix (Fin 2) (Fin 2) ℝ).det‖ = 1
    rw [hdet, norm_one]
  · intro x y
    show ‖x * p + y * (-q)‖ ^ 2 + ‖x * q + y * p‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [hpq]

theorem iwasawa (h : GL (Fin 2) ℝ) :
    ∃ (x : ℝ) (t z : ℝˣ) (κ : GL (Fin 2) ℝ) (_ : κ ∈ rowIsometrySubgroup₀ ℝ),
      h = unipotentGL2 x * diagOne t * Matrix.GeneralLinearGroup.scalar (Fin 2) z * κ := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : ℝ, (h : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c ≠ 0 := by
    have h1 : (h : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det h).ne_zero
    rwa [hM, Matrix.det_fin_two_of] at h1
  have hD : 0 < c ^ 2 + d ^ 2 := by
    rcases eq_or_ne c 0 with hc0 | hc0
    · have hd0 : d ≠ 0 := by intro hd0; apply hdet; rw [hc0, hd0]; ring
      positivity
    · positivity
  have hDne : c ^ 2 + d ^ 2 ≠ 0 := hD.ne'
  set r : ℝ := Real.sqrt (c ^ 2 + d ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hD
  have hr2 : r ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt hD.le
  have hrne : r ≠ 0 := hr0.ne'
  have hpq : (d / r) ^ 2 + (-c / r) ^ 2 = 1 := by
    rw [div_pow, div_pow, hr2]; field_simp; ring
  have ht0 : (a * d - b * c) / (c ^ 2 + d ^ 2) ≠ 0 := div_ne_zero hdet hDne
  refine ⟨(a * c + b * d) / (c ^ 2 + d ^ 2), Units.mk0 _ ht0, Units.mk0 r hrne,
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![d / r, -c / r; -(-c / r), d / r]
      (by rw [Matrix.det_fin_two_of]; nlinarith),
    rot_mem (d / r) (-c / r) hpq, ?_⟩
  refine Units.ext ?_
  rw [hM]
  ext i j
  simp only [Units.val_mul, unipotentGL2_coe, Matrix.GeneralLinearGroup.scalar,
    Units.coe_map, Units.val_mk0, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [diagOne_coe_apply, Matrix.diagonal, Matrix.GeneralLinearGroup.mkOfDetNeZero] <;>
    field_simp <;> ring

theorem continuous_eR_symm (v : InfinitePlace ℚ) :
    Continuous fun x : ℝ => (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm x :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous

theorem iotaR_entry (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      ((fun v => (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j),
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Prod.ext (funext fun v => iotaR_fst M i j v) (iotaR_snd M i j)

theorem continuous_iotaR_val : Continuous fun M : GL (Fin 2) ℝ => ((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp_rw [iotaR_entry]
  exact (continuous_pi fun v => (continuous_eR_symm v).comp
    ((Units.continuous_val.matrix_elem i j))).prodMk continuous_const

theorem continuous_iotaR : Continuous (ιR : GL (Fin 2) ℝ → G2) := by
  refine Units.continuous_iff.2 ⟨continuous_iotaR_val, ?_⟩
  have : (fun M : GL (Fin 2) ℝ => (((ιR M)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸)) =
      fun M => ((ιR M⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸) := by
    funext M; rw [map_inv]
  rw [this]
  exact continuous_iotaR_val.comp continuous_inv

theorem continuous_Wφ (D : Set G2) {φ : G2 → ℂ} (hφc : Continuous φ) : Continuous (Wφ D φ) := by
  haveI : SecondCountableTopology G2 := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo ℚ
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μA (adelicBox ℚ)) := isProbabilityMeasure_cond_adelicBox ℚ
  have hF : Continuous fun p : G2 × 𝔸 => φ (unipotentGL2 p.2 * p.1) * NumberField.StandardAddChar.psiQ (-p.2) := by
    have hn : Continuous fun p : G2 × 𝔸 => (unipotentGL2 p.2 : G2) :=
      (AutomorphicForm.continuous_unipotentGL2 (R := 𝔸)).comp continuous_snd
    exact (hφc.comp (hn.mul continuous_fst)).mul
      (NumberField.StandardAddChar.continuous_psiQ.comp continuous_snd.neg)
  have heq : Wφ D φ = fun g => ∫ x, φ (unipotentGL2 x * g) * NumberField.StandardAddChar.psiQ (-x)
      ∂(ProbabilityTheory.cond μA (adelicBox ℚ)) := funext (Wφ_apply D φ)
  rw [heq]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g₀
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset ℚ
  obtain ⟨B, hB⟩ := (hK.prod hC).exists_bound_of_continuousOn (f := fun p : G2 × 𝔸 =>
    φ (unipotentGL2 p.2 * p.1) * NumberField.StandardAddChar.psiQ (-p.2)) hF.continuousOn
  have hae : ∀ᵐ x ∂(ProbabilityTheory.cond μA (adelicBox ℚ)), x ∈ adelicBox ℚ :=
    ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox ℚ)
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · exact Filter.Eventually.of_forall fun g =>
      (hF.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · filter_upwards [hKg] with g hg
    filter_upwards [hae] with x hx
    exact hB (g, x) ⟨hg, hBC hx⟩
  · exact Filter.Eventually.of_forall fun x =>
      (hF.comp (Continuous.prodMk continuous_id continuous_const)).continuousAt

section Master

variable {D : Set G2} {ξ : (pinsQ D).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  {Φ : HeckeEigensystem ℚ ℂ} {φ : G2 → ℂ} {Wr : InfinitePlace ℚ → ℂ → ℂ} {k : InfinitePlace ℚ → ℤ}
  {C : FiniteAdeleRing (𝓞 ℚ) ℚ → G2 → ℂ}

theorem master (hiso : IsIsotypicCuspFormAt ℚ (pinsQ D) ξ N S Φ φ)
    (harch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    (hφW : ∀ a : (𝔸)ˣ, ∀ g : G2, g ∈ finiteAdelicGL2Subgroup ℚ →
      Wφ D φ (diagOne a * g)
        = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : 𝔸).1 w))) * C (a : 𝔸).2 g)
    (x : ℝ) (t z : ℝˣ) (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) {g : G2}
    (hg : g ∈ finiteAdelicGL2Subgroup ℚ) :
    Wφ D φ (ιR (unipotentGL2 x * diagOne t * Matrix.GeneralLinearGroup.scalar (Fin 2) z * κ) * g) =
      Complex.exp (2 * Real.pi * Complex.I * x) *
        (((ξ.comp Subgroup.topEquiv.symm.toMonoidHom (uR z) : ℂˣ) : ℂ) *
          ((archWeightCharℝ (k default) ⟨κ, hκ⟩ : ℂ) * (Wr default (t : ℝ) * C 1 g))) := by
  have e1 : ιR (unipotentGL2 x * diagOne t * Matrix.GeneralLinearGroup.scalar (Fin 2) z * κ) * g =
      unipotentGL2 (aR x) * (centralScalar (𝓞 ℚ) ℚ (uR z) * (ιR (diagOne t) * g * ιR κ)) := by
    rw [map_mul, map_mul, map_mul, iotaR_unipotentGL2, iotaR_scalar]
    simp only [mul_assoc]
    rw [iotaR_mul_comm hg κ]
    congr 1
    rw [← mul_assoc, ← centralScalar_comm (uR z) (ιR (diagOne t)), mul_assoc]
  rw [e1, Wφ_unipotentGL2_mul (left_invariant_of_iso hiso), psiQ_aR, Wφ_centralScalar_mul hiso,
    Wφ_mul_iotaR_kappa harch κ hκ, Wφ_iotaR_diagOne_mul hφW t hg]

end Master

end Ws23FactPhi
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt.Ws23FactPhi"

open Ws23FactPhi in

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ)
    (C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hiso : IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ N S Φ φ)
    (_harch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ)
    (_hφW : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      whittakerCoefficient ℚ
          (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
            (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
        = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
            * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (_hW : whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ 1 ≠ 0) :
    ∃ (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ),
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ
            (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
              (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
            NumberField.StandardAddChar.psiQ φ 1 g
          = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g)) ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ, Wf g = C 1 (g : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      (∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA h) ∧
      (∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = (TateGlobal.archLocalChar (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) default
              (Units.map (ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).symm.toMonoidHom z)
              : ℂ) * WA h) ∧
      (∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA (h * κ) = (archWeightCharℝ (k default) ⟨κ, hκ⟩ : ℂ) * WA h) ∧
      (∀ t : ℝˣ, WA (diagOne t) = Wr default (t : ℝ)) ∧
      Continuous WA := by

  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.1 _hW
  have hdec : ∀ g : G2, g = ιR (ratArchGL2 g) * (RSCarrier.finFactor g : G2) := fun g =>
    (mul_inv_cancel_left (ιR (ratArchGL2 g)) g).symm
  obtain ⟨x₁, t₁, z₁, κ₁, hκ₁, hI₁⟩ := iwasawa (ratArchGL2 g₁)
  have hc₀ : C 1 (RSCarrier.finFactor g₁ : G2) ≠ 0 := by
    intro h0
    apply hg₁
    show Wφ D φ g₁ = 0
    rw [hdec g₁, hI₁, master _hiso _harch _hφW x₁ t₁ z₁ κ₁ hκ₁ (RSCarrier.finFactor g₁).2, h0]
    simp
  refine ⟨fun h => Wφ D φ (ιR h * (RSCarrier.finFactor g₁ : G2)) / C 1 (RSCarrier.finFactor g₁ : G2),
    fun g => C 1 (g : G2), ?_, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g
    obtain ⟨x, t, z, κ, hκ, hI⟩ := iwasawa (ratArchGL2 g)
    show Wφ D φ g = _
    conv_lhs => rw [hdec g]
    simp only
    rw [hI, master _hiso _harch _hφW x t z κ hκ (RSCarrier.finFactor g).2,
      master _hiso _harch _hφW x t z κ hκ (RSCarrier.finFactor g₁).2]
    field_simp
  ·
    intro x h
    simp only
    rw [map_mul, iotaR_unipotentGL2, mul_assoc, Wφ_unipotentGL2_mul (left_invariant_of_iso _hiso), psiQ_aR,
      mul_div_assoc]
  ·
    intro z h
    simp only
    rw [map_mul, iotaR_scalar, mul_assoc, Wφ_centralScalar_mul _hiso, mul_div_assoc]
    rfl
  ·
    intro κ hκ h
    simp only
    rw [map_mul, mul_assoc, iotaR_mul_comm (RSCarrier.finFactor g₁).2 κ, ← mul_assoc,
      Wφ_mul_iotaR_kappa _harch κ hκ, mul_div_assoc]
  ·
    intro t
    simp only
    rw [Wφ_iotaR_diagOne_mul _hφW t (RSCarrier.finFactor g₁).2, mul_div_cancel_right₀ _ hc₀]
  ·
    exact ((continuous_Wφ D _hiso.continuous).comp (continuous_iotaR.mul continuous_const)).div_const _

end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt.Ws23FactPhi"

end S_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt
end P2MW
export P2MW.S_LanglandsTunnell_exists_whittakerCoefficient_eq_archWhittaker_mul_finWhittaker_of_isIsotypicCuspFormAt (solution)
