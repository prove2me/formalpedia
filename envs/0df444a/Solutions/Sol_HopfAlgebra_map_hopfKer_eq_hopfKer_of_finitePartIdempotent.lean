-- Prove2me | solution 1 for HopfAlgebra.map_hopfKer_eq_hopfKer_of_finitePartIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a1d4c98d-226a-596a-aa34-ff268950f100

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq
import Theorems.Thm_Algebra_TensorProduct_exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq
import Theorems.Thm_HopfAlgebra_mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing
import Theorems.Thm_IsLocalRing_exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top
import Theorems.Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange
import Theorems.Thm_HopfAlgebra_comul_finitePartIdempotent_mul
import Theorems.Thm_HopfAlgebra_counit_finitePartIdempotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false

open scoped TensorProduct

namespace FltWs11
namespace QS

open HopfAlgebra

variable {R : Type} [CommRing R]
  {H : Type} [CommRing H] [HopfAlgebra R H] {H' : Type} [CommRing H'] [HopfAlgebra R H']
  {Hf : Type} [CommRing Hf] [HopfAlgebra R Hf] {Hf' : Type} [CommRing Hf'] [HopfAlgebra R Hf']

theorem map_id_comp_map_eq (qc : H →ₐc[R] H') (πf : H →ₐc[R] Hf) (πf' : H' →ₐc[R] Hf') (qcf : Hf →ₐc[R] Hf')
    (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x)) :
    (Algebra.TensorProduct.map (AlgHom.id R Hf) (qcf : Hf →ₐ[R] Hf')).comp
        (Algebra.TensorProduct.map (πf : H →ₐ[R] Hf) (πf : H →ₐ[R] Hf))
      = (Algebra.TensorProduct.map (πf : H →ₐ[R] Hf) (πf' : H' →ₐ[R] Hf')).comp
        (Algebra.TensorProduct.map (AlgHom.id R H) (qc : H →ₐ[R] H')) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  show (πf : H →ₐ[R] Hf) a ⊗ₜ[R] (qcf : Hf →ₐ[R] Hf') ((πf : H →ₐ[R] Hf) b)
    = (πf : H →ₐ[R] Hf) a ⊗ₜ[R] (πf' : H' →ₐ[R] Hf') ((qc : H →ₐ[R] H') b)
  congr 1
  exact hcomm b

theorem map_coaction_eq (qc : H →ₐc[R] H') (πf : H →ₐc[R] Hf) (πf' : H' →ₐc[R] Hf') (qcf : Hf →ₐc[R] Hf')
    (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x)) (b : H) :
    coaction qcf (πf b)
      = Algebra.TensorProduct.map (πf : H →ₐ[R] Hf) (πf' : H' →ₐ[R] Hf') (coaction qc b) := by
  rw [coaction_apply, coaction_apply]
  have h1 : Coalgebra.comul (R := R) (πf b)
      = Algebra.TensorProduct.map (πf : H →ₐ[R] Hf) (πf : H →ₐ[R] Hf) (Coalgebra.comul (R := R) b) :=
    (AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom πf) b).symm
  rw [h1]
  exact AlgHom.congr_fun (map_id_comp_map_eq qc πf πf' qcf hcomm) (Coalgebra.comul (R := R) b)

theorem map_hopfKer_le (qc : H →ₐc[R] H') (πf : H →ₐc[R] Hf) (πf' : H' →ₐc[R] Hf') (qcf : Hf →ₐc[R] Hf')
    (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x)) :
    (hopfKer qc).map (πf : H →ₐ[R] Hf) ≤ hopfKer qcf := by
  rintro _ ⟨b, hb, rfl⟩
  change coaction qcf (πf b) = (πf : H →ₐ[R] Hf) b ⊗ₜ[R] (1 : Hf')
  rw [map_coaction_eq qc πf πf' qcf hcomm b, coaction_eq_of_mem qc hb, Algebra.TensorProduct.map_tmul,
    map_one]

end FltWs11.QS

open scoped TensorProduct

namespace FltWs11
namespace RED

open HopfAlgebra Algebra.TensorProduct

variable {R : Type} [CommRing R] (K : Type) [CommRing K] [Algebra R K]
  {H : Type} [CommRing H] [HopfAlgebra R H] {H' : Type} [CommRing H'] [HopfAlgebra R H']

noncomputable def bcPair : H ⊗[R] H' →ₐ[R] (K ⊗[R] H) ⊗[K] (K ⊗[R] H') :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : K ⊗[R] H →ₐ[K] (K ⊗[R] H) ⊗[K] (K ⊗[R] H')).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H))
    (((Algebra.TensorProduct.includeRight : K ⊗[R] H' →ₐ[K] (K ⊗[R] H) ⊗[K] (K ⊗[R] H')).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H' →ₐ[R] K ⊗[R] H'))
    (fun x y => Commute.all (S := (K ⊗[R] H) ⊗[K] (K ⊗[R] H')) _ _)

@[scoped simp] theorem bcPair_tmul (u : H) (v : H') :
    bcPair K (u ⊗ₜ[R] v) = ((1 : K) ⊗ₜ[R] u) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] v) := by
  simp [bcPair, Algebra.TensorProduct.tmul_mul_tmul]

set_option synthInstance.maxHeartbeats 320000 in

theorem comul_one_tmul (h : H) :
    Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[R] h) = bcPair K (Coalgebra.comul (R := R) h) := by
  rw [TensorProduct.comul_tmul]
  have h1 : Coalgebra.comul (R := K) (1 : K) = (1 : K) ⊗ₜ[K] (1 : K) := by
    simp
  rw [h1]
  induction (Coalgebra.comul (R := R) h) using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem coaction_one_tmul (qc : H →ₐc[R] H') (x : H) :
    coaction (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H') ((1 : K) ⊗ₜ[R] x)
      = bcPair K (coaction qc x) := by
  rw [coaction_apply, coaction_apply, comul_one_tmul]
  induction (Coalgebra.comul (R := R) x) using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [bcPair_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem one_tmul_mem_hopfKer (qc : H →ₐc[R] H') {x : H} (hx : x ∈ hopfKer qc) :
    ((1 : K) ⊗ₜ[R] x) ∈ hopfKer (Bialgebra.TensorProduct.map (BialgHom.id K K) qc :
      K ⊗[R] H →ₐc[K] K ⊗[R] H') := by
  change coaction _ _ = _
  rw [coaction_one_tmul, coaction_eq_of_mem qc hx, bcPair_tmul]
  rfl

end FltWs11.RED
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11"

namespace FltWs11
namespace RED

open HopfAlgebra Algebra.TensorProduct

section

variable {R : Type} [CommRing R] (K : Type) [CommRing K] [Algebra R K]
  {H : Type} [CommRing H] [HopfAlgebra R H]

theorem comul_one_tmul_mul_of {e : H}
    (hΔ : Coalgebra.comul (R := R) e * (e ⊗ₜ[R] (1 : H)) = e ⊗ₜ[R] e) :
    Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[R] e) * (((1 : K) ⊗ₜ[R] e) ⊗ₜ[K] (1 : K ⊗[R] H))
      = ((1 : K) ⊗ₜ[R] e) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] e) := by
  have h1 : ((1 : K) ⊗ₜ[R] e) ⊗ₜ[K] (1 : K ⊗[R] H) = bcPair K (e ⊗ₜ[R] (1 : H)) := by
    rw [bcPair_tmul, Algebra.TensorProduct.one_def]
  rw [comul_one_tmul, h1, ← map_mul, hΔ, bcPair_tmul]

theorem counit_one_tmul_of {e : H} (hε : Coalgebra.counit (R := R) e = 1) :
    Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[R] e) = 1 := by
  rw [TensorProduct.counit_tmul, hε, one_smul]
  simp

end
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"

section

variable {R : Type} [CommRing R] (K : Type) [CommRing K] [Algebra R K]
  {H : Type} [CommRing H] [HopfAlgebra R H] {H' : Type} [CommRing H'] [HopfAlgebra R H']
  {Hf : Type} [CommRing Hf] [HopfAlgebra R Hf] {Hf' : Type} [CommRing Hf'] [HopfAlgebra R Hf']

theorem hcomm_baseChange (qc : H →ₐc[R] H') (πf : H →ₐc[R] Hf) (πf' : H' →ₐc[R] Hf')
    (qcf : Hf →ₐc[R] Hf') (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x)) :
    ∀ z : K ⊗[R] H,
      Bialgebra.TensorProduct.map (BialgHom.id K K) qcf (Bialgebra.TensorProduct.map (BialgHom.id K K) πf z)
        = Bialgebra.TensorProduct.map (BialgHom.id K K) πf' (Bialgebra.TensorProduct.map (BialgHom.id K K) qc z) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x => simp [Bialgebra.TensorProduct.map_tmul, hcomm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ker_baseChange_eq (πf : H →ₐc[R] Hf) (hπf : Function.Surjective πf) {e : H}
    (hkerf : RingHom.ker (πf : H →ₐ[R] Hf) = Ideal.span {1 - e}) :
    RingHom.ker ((Bialgebra.TensorProduct.map (BialgHom.id K K) πf : K ⊗[R] H →ₐc[K] K ⊗[R] Hf) :
        K ⊗[R] H →ₐ[K] K ⊗[R] Hf)
      = Ideal.span {1 - (1 : K) ⊗ₜ[R] e} := by
  have h0 : ∀ z : K ⊗[R] H, (Bialgebra.TensorProduct.map (BialgHom.id K K) πf : K ⊗[R] H →ₐc[K] K ⊗[R] Hf) z
      = Algebra.TensorProduct.map (AlgHom.id R K) (πf : H →ₐ[R] Hf) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 : RingHom.ker ((Bialgebra.TensorProduct.map (BialgHom.id K K) πf : K ⊗[R] H →ₐc[K] K ⊗[R] Hf) :
        K ⊗[R] H →ₐ[K] K ⊗[R] Hf)
      = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R K) (πf : H →ₐ[R] Hf)) := by
    ext z
    simp only [RingHom.mem_ker]
    rw [← h0 z]
    rfl
  rw [h1, Algebra.TensorProduct.lTensor_ker (πf : H →ₐ[R] Hf) hπf, hkerf, Ideal.map_span, Set.image_singleton]
  congr 1
  simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]

end
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"

section Denominators

variable {R : Type} [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Flat R H] {H' : Type} [CommRing H'] [HopfAlgebra R H']

theorem exists_smul_eq_one_tmul_of_mem_hopfKer (qc : H →ₐc[R] H')
    {b : K ⊗[R] H} (hb : b ∈ hopfKer (Bialgebra.TensorProduct.map (BialgHom.id K K) qc :
      K ⊗[R] H →ₐc[K] K ⊗[R] H')) :
    ∃ (d : R) (b₀ : H), d ≠ 0 ∧ b₀ ∈ hopfKer qc ∧ (algebraMap R K d) • b = (1 : K) ⊗ₜ[R] b₀ := by
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hrange := HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange K qc
  have hb' : b ∈ Subalgebra.toSubmodule (hopfKer (Bialgebra.TensorProduct.map (BialgHom.id K K) qc :
      K ⊗[R] H →ₐc[K] K ⊗[R] H')) := hb
  rw [hrange] at hb'
  obtain ⟨γ, rfl⟩ := hb'

  haveI : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K ↥(hopfKer qc) 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).mpr (TensorProduct.isBaseChange R ↥(hopfKer qc) K)
  obtain ⟨⟨b₀, d⟩, hd⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K ↥(hopfKer qc) 1) γ
  refine ⟨d.1, b₀.1, nonZeroDivisors.ne_zero d.2, b₀.2, ?_⟩

  have := congrArg ((hopfKer qc).val.toLinearMap.baseChange K) hd
  rw [LinearMap.map_smul_of_tower] at this
  simp [LinearMap.baseChange_tmul, algebraMap_smul] at this ⊢
  exact this

end Denominators
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"

end FltWs11.RED
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"

namespace FltWs11
namespace RED

open HopfAlgebra Algebra.TensorProduct

section Tools

variable {R : Type} [CommRing R] (K : Type) [CommRing K] [Algebra R K]
  {H : Type} [CommRing H] [HopfAlgebra R H] {H' : Type} [CommRing H'] [HopfAlgebra R H']

theorem bc_apply (g : H →ₐc[R] H') (z : K ⊗[R] H) :
    (Bialgebra.TensorProduct.map (BialgHom.id K K) g : K ⊗[R] H →ₐc[K] K ⊗[R] H') z
      = Algebra.TensorProduct.map (AlgHom.id K K) (g : H →ₐ[R] H') z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bc_surjective (g : H →ₐc[R] H') (hg : Function.Surjective g) :
    Function.Surjective (Bialgebra.TensorProduct.map (BialgHom.id K K) g : K ⊗[R] H →ₐc[K] K ⊗[R] H') := by
  have key : ∀ w : K ⊗[R] H, (Bialgebra.TensorProduct.map (BialgHom.id K K) g : K ⊗[R] H →ₐc[K] K ⊗[R] H') w
      = LinearMap.lTensor K (g : H →ₗ[R] H') w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul k x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro z
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective K (g := (g : H →ₗ[R] H')) hg z
  exact ⟨w, by rw [key, hw]⟩

end Tools
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"

section Main

variable (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0)
    (Hf : Type) [CommRing Hf] [HopfAlgebra R Hf] (πf : H →ₐc[R] Hf) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker (πf : H →ₐ[R] Hf) = Ideal.span {1 - e})
    (Hf' : Type) [CommRing Hf'] [HopfAlgebra R Hf'] (πf' : H' →ₐc[R] Hf') (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker (πf' : H' →ₐ[R] Hf') = Ideal.span {1 - e'})
    (qcf : Hf →ₐc[R] Hf') (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x))

include K hqc he hfin hgen hee' hf hfK hfe hmin hπf hkerf hπf' hkerf' hcomm in

theorem map_hopfKer_eq : (hopfKer qc).map (πf : H →ₐ[R] Hf) = hopfKer qcf := by
  classical
  apply le_antisymm (FltWs11.QS.map_hopfKer_le qc πf πf' qcf hcomm)
  intro a ha

  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hinjRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let πK : K ⊗[R] H →ₐc[K] K ⊗[R] H' := Bialgebra.TensorProduct.map (BialgHom.id K K) qc
  let πfK : K ⊗[R] H →ₐc[K] K ⊗[R] Hf := Bialgebra.TensorProduct.map (BialgHom.id K K) πf
  let πf'K : K ⊗[R] H' →ₐc[K] K ⊗[R] Hf' := Bialgebra.TensorProduct.map (BialgHom.id K K) πf'
  let qcfK : K ⊗[R] Hf →ₐc[K] K ⊗[R] Hf' := Bialgebra.TensorProduct.map (BialgHom.id K K) qcf
  have heK : IsIdempotentElem ((1 : K) ⊗ₜ[R] e) := by
    change _ * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.eq]
  have hfKi : IsIdempotentElem ((1 : K) ⊗ₜ[R] f) := by
    change _ * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hf.eq]
  have hΔ := comul_one_tmul_mul_of K (HopfAlgebra.comul_finitePartIdempotent_mul R H e he hfin hgen).1
  have hε := counit_one_tmul_of K (HopfAlgebra.counit_finitePartIdempotent R H e he hgen)
  have hfKK : ((1 : K) ⊗ₜ[R] f) ∈ hopfKer πK := one_tmul_mem_hopfKer K qc hfK
  have hfeK : ((1 : K) ⊗ₜ[R] f) * ((1 : K) ⊗ₜ[R] e) = (1 : K) ⊗ₜ[R] e := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hfe]
  have hminK : ∀ b ∈ hopfKer πK, b * ((1 : K) ⊗ₜ[R] e) = 0 → b * ((1 : K) ⊗ₜ[R] f) = 0 := by
    intro b hb hbe
    obtain ⟨d, b₀, hd, hb₀, hdb⟩ := exists_smul_eq_one_tmul_of_mem_hopfKer K qc hb
    have hd' : algebraMap R K d ≠ 0 := fun h => hd (hinjRK (by rw [h, map_zero]))
    have h1 : ((1 : K) ⊗ₜ[R] (b₀ * e)) = 0 := by
      rw [← one_mul (1 : K), ← Algebra.TensorProduct.tmul_mul_tmul, ← hdb, smul_mul_assoc, hbe, smul_zero]
    have h2 : b₀ * e = 0 := by
      apply Algebra.TensorProduct.includeRight_injective (A := K) hinjRK
      rw [Algebra.TensorProduct.includeRight_apply, h1, map_zero]
    have h3 : b₀ * f = 0 := hmin b₀ hb₀ h2
    have h4 : algebraMap R K d • (b * ((1 : K) ⊗ₜ[R] f)) = 0 := by
      rw [← smul_mul_assoc, hdb, Algebra.TensorProduct.tmul_mul_tmul, one_mul, h3, TensorProduct.tmul_zero]
    exact (smul_eq_zero.mp h4).resolve_left hd'
  have hkerfK : RingHom.ker (πfK : K ⊗[R] H →ₐ[K] K ⊗[R] Hf) = Ideal.span {1 - (1 : K) ⊗ₜ[R] e} :=
    ker_baseChange_eq K πf hπf hkerf
  have hπKe : πK ((1 : K) ⊗ₜ[R] e) = (1 : K) ⊗ₜ[R] e' := by
    change Bialgebra.TensorProduct.map (BialgHom.id K K) qc ((1 : K) ⊗ₜ[R] e) = _
    rw [Bialgebra.TensorProduct.map_tmul, hee']
    rfl
  have hkerf'K : RingHom.ker (πf'K : K ⊗[R] H' →ₐ[K] K ⊗[R] Hf') = Ideal.span {1 - πK ((1 : K) ⊗ₜ[R] e)} := by
    rw [hπKe]
    exact ker_baseChange_eq K πf' hπf' hkerf'
  have hFC := HopfAlgebra.map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq K (K ⊗[R] H) (K ⊗[R] H') πK
    (bc_surjective K qc hqc) ((1 : K) ⊗ₜ[R] e) heK hΔ hε ((1 : K) ⊗ₜ[R] f) hfKi hfKK hfeK hminK
    (K ⊗[R] Hf) πfK (bc_surjective K πf hπf) hkerfK (K ⊗[R] Hf') πf'K (bc_surjective K πf' hπf') hkerf'K
    qcfK (hcomm_baseChange K qc πf πf' qcf hcomm)

  have ha' : ((1 : K) ⊗ₜ[R] a) ∈ hopfKer qcfK := one_tmul_mem_hopfKer K qcf ha
  rw [← hFC] at ha'
  obtain ⟨β, hβ, hβa⟩ := ha'

  have hπfe : (πf : H →ₐ[R] Hf) e = 1 := by
    have : (1 - e) ∈ RingHom.ker (πf : H →ₐ[R] Hf) := by rw [hkerf]; exact Ideal.subset_span rfl
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have hπff : (πf : H →ₐ[R] Hf) f = 1 := by
    have := congrArg (πf : H →ₐ[R] Hf) hfe
    rwa [map_mul, hπfe, mul_one] at this
  set β' := β * ((1 : K) ⊗ₜ[R] f) with hβ'def
  have hβ'f : β' * ((1 : K) ⊗ₜ[R] f) = β' := by
    rw [hβ'def, mul_assoc, hfKi.eq]
  have hβaB : πfK β = (1 : K) ⊗ₜ[R] a := hβa
  have hπfKf : πfK ((1 : K) ⊗ₜ[R] f) = (1 : K) ⊗ₜ[R] ((πf : H →ₐ[R] Hf) f) := rfl
  have hβ'a : Algebra.TensorProduct.map (AlgHom.id K K) (πf : H →ₐ[R] Hf) β' = (1 : K) ⊗ₜ[R] a := by
    rw [← bc_apply K πf, hβ'def, map_mul, hβaB, hπfKf, hπff, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one]

  have hdiv := IsLocalRing.exists_smul_mul_one_sub_eq_of_map_maximalIdeal_eq_top R H e he hgen
  obtain ⟨h, hβh, hπh⟩ :=
    Algebra.TensorProduct.exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq R K H e f he hf hfe hdiv
      Hf (πf : H →ₐ[R] Hf) hπf hkerf β' hβ'f a hβ'a

  have hβ'mem : β' ∈ hopfKer πK := Subalgebra.mul_mem _ hβ hfKK
  have hh : h ∈ hopfKer qc := by
    rw [HopfAlgebra.mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing K qc h, ← hβh]
    exact hβ'mem
  exact ⟨h, hh, hπh⟩

end Main
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"

end FltWs11.RED
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"
p2m_reactivate "P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11 P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.FltWs11.RED"

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0)
    (Hf : Type) [CommRing Hf] [HopfAlgebra R Hf] (πf : H →ₐc[R] Hf) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker (πf : H →ₐ[R] Hf) = Ideal.span {1 - e})
    (Hf' : Type) [CommRing Hf'] [HopfAlgebra R Hf'] (πf' : H' →ₐc[R] Hf') (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker (πf' : H' →ₐ[R] Hf') = Ideal.span {1 - e'})
    (qcf : Hf →ₐc[R] Hf') (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x)) :
    (HopfAlgebra.hopfKer qc).map (πf : H →ₐ[R] Hf) = HopfAlgebra.hopfKer qcf :=
  FltWs11.RED.map_hopfKer_eq R K H H' qc hqc e he hfin hgen e' hee' f hf hfK hfe hmin
    Hf πf hπf hkerf Hf' πf' hπf' hkerf' qcf hcomm

end S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent
end P2MW
export P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent (solution)
