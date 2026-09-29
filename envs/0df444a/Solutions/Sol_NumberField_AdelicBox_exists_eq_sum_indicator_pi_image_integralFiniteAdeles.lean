-- Prove2me | solution 1 for NumberField.AdelicBox.exists_eq_sum_indicator_pi_image_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8ff0bd54-0044-538e-8c84-5ef41524734e

import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles.NumberField NumberField.AdelicBox P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles.NumberField.AdelicBox IsDedekindDomain Topology Filter"
open scoped Pointwise

noncomputable section

namespace NumberField
p2m_export "NumberField" "RingOfIntegers RingOfIntegers.coe_ne_zero_iff AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles"
namespace AdelicBox
p2m_export "NumberField.AdelicBox" "integralFiniteAdeles algebraMap_mem_adicCompletionIntegers exists_algebraMap_add_mem_integralFiniteAdeles isClosed_integralFiniteAdeles isCompact_integralFiniteAdeles isOpen_integralFiniteAdeles exists_eq_sum_indicator_image_integralFiniteAdeles"
namespace PiDecomposition
p2m_open "NumberField.AdelicBox NumberField"

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

abbrev ιF (F : Type) [Field F] [NumberField F] : F →+* FiniteAdeleRing (𝓞 F) F :=
  algebraMap F (FiniteAdeleRing (𝓞 F) F)

def coset (d : 𝓞 F) (k : F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ ιF F k + ιF F (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

theorem zero_mem_integral : (0 : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => (v.adicCompletionIntegers F).zero_mem

theorem add_mem_integral {x y : FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ integralFiniteAdeles (𝓞 F) F) (hy : y ∈ integralFiniteAdeles (𝓞 F) F) :
    x + y ∈ integralFiniteAdeles (𝓞 F) F := fun v => add_mem (hx v) (hy v)

theorem neg_mem_integral {x : FiniteAdeleRing (𝓞 F) F} (hx : x ∈ integralFiniteAdeles (𝓞 F) F) :
    -x ∈ integralFiniteAdeles (𝓞 F) F := fun v => neg_mem (hx v)

theorem sub_mem_integral {x y : FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ integralFiniteAdeles (𝓞 F) F) (hy : y ∈ integralFiniteAdeles (𝓞 F) F) :
    x - y ∈ integralFiniteAdeles (𝓞 F) F := fun v => sub_mem (hx v) (hy v)

theorem mul_mem_integral {x y : FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ integralFiniteAdeles (𝓞 F) F) (hy : y ∈ integralFiniteAdeles (𝓞 F) F) :
    x * y ∈ integralFiniteAdeles (𝓞 F) F := fun v => mul_mem (hx v) (hy v)

theorem algebraMap_int_mem_integral (a : 𝓞 F) :
    ιF F (a : F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a

theorem inv_mul_cancel_alg {d : 𝓞 F} (hd : d ≠ 0) :
    ιF F ((d : F)⁻¹) * ιF F (d : F) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.mpr hd), map_one]

theorem mul_inv_cancel_alg {d : 𝓞 F} (hd : d ≠ 0) :
    ιF F (d : F) * ιF F ((d : F)⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (RingOfIntegers.coe_ne_zero_iff.mpr hd), map_one]

theorem mem_coset_iff {d : 𝓞 F} (hd : d ≠ 0) (k : F) (v : FiniteAdeleRing (𝓞 F) F) :
    v ∈ coset d k ↔ ιF F ((d : F)⁻¹) * (v - ιF F k) ∈ integralFiniteAdeles (𝓞 F) F := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have : ιF F ((d : F)⁻¹) * (ιF F k + ιF F (d : F) * z - ιF F k) = z := by
      rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel_alg hd, one_mul]
    rw [this]; exact hz
  · intro h
    refine ⟨ιF F ((d : F)⁻¹) * (v - ιF F k), h, ?_⟩
    show ιF F k + ιF F (d : F) * (ιF F ((d : F)⁻¹) * (v - ιF F k)) = v
    rw [← mul_assoc, mul_inv_cancel_alg hd, one_mul, add_sub_cancel]

theorem mem_coset_iff_of_mem {d : 𝓞 F} (hd : d ≠ 0) {k : F} {v : FiniteAdeleRing (𝓞 F) F}
    (hv : v ∈ coset d k) (u : FiniteAdeleRing (𝓞 F) F) :
    u ∈ coset d k ↔ ιF F ((d : F)⁻¹) * (u - v) ∈ integralFiniteAdeles (𝓞 F) F := by
  rw [mem_coset_iff hd] at hv ⊢
  have hsplit : ιF F ((d : F)⁻¹) * (u - ιF F k)
      = ιF F ((d : F)⁻¹) * (u - v) + ιF F ((d : F)⁻¹) * (v - ιF F k) := by ring
  constructor
  · intro hu
    have := sub_mem_integral hu hv
    rwa [hsplit, add_sub_cancel_right] at this
  · intro hu
    rw [hsplit]
    exact add_mem_integral hu hv

theorem coset_eq_of_mem {d : 𝓞 F} (hd : d ≠ 0) {k k' : F} {v : FiniteAdeleRing (𝓞 F) F}
    (hv : v ∈ coset d k) (hv' : v ∈ coset d k') : coset d k = coset d k' := by
  ext u
  rw [mem_coset_iff_of_mem hd hv, mem_coset_iff_of_mem hd hv']

theorem isOpen_coset {d : 𝓞 F} (hd : d ≠ 0) (k : F) : IsOpen (coset d k) := by
  have : coset d k = (fun v => ιF F ((d : F)⁻¹) * (v - ιF F k)) ⁻¹' integralFiniteAdeles (𝓞 F) F := by
    ext v; exact mem_coset_iff hd k v
  rw [this]
  exact (isOpen_integralFiniteAdeles F).preimage
    ((continuous_const.mul (continuous_id.sub continuous_const)))

theorem algebraMap_mem_coset (d : 𝓞 F) (k : F) : ιF F k ∈ coset d k :=
  ⟨0, zero_mem_integral, by simp⟩

theorem add_mul_mem_coset {d : 𝓞 F} (hd : d ≠ 0) {k : F} {v : FiniteAdeleRing (𝓞 F) F}
    (hv : v ∈ coset d k) {z : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    v + ιF F (d : F) * z ∈ coset d k := by
  rw [mem_coset_iff_of_mem hd hv]
  have : ιF F ((d : F)⁻¹) * (v + ιF F (d : F) * z - v) = z := by
    rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel_alg hd, one_mul]
  rw [this]; exact hz

theorem isLocallyConstant_indicator_of_isClopen {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsClopen S) : IsLocallyConstant (S.indicator (1 : X → ℂ)) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ S
  · exact ⟨S, hS.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply]⟩
  · exact ⟨Sᶜ, hS.compl.isOpen, hx, fun y hy =>
      by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem exists_mul_integral_subset_of_mem_nhds (H₁ : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hH : (H₁ : Set (FiniteAdeleRing (𝓞 F) F)) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ιF F (d : F) * z ∈ H₁ := by
  have hopen : IsOpen (H₁ : Set (FiniteAdeleRing (𝓞 F) F)) := H₁.isOpen_of_mem_nhds hH
  have hclosed : IsClosed (H₁ : Set (FiniteAdeleRing (𝓞 F) F)) := H₁.isClosed_of_isOpen hopen
  set S : Set (FiniteAdeleRing (𝓞 F) F) := (H₁ : Set _) ∩ integralFiniteAdeles (𝓞 F) F with hS
  have hSclopen : IsClopen S :=
    ⟨hclosed.inter (isClosed_integralFiniteAdeles F), hopen.inter (isOpen_integralFiniteAdeles F)⟩
  have hlc : IsLocallyConstant (S.indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) :=
    isLocallyConstant_indicator_of_isClopen hSclopen
  have hcs : HasCompactSupport (S.indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) := by
    refine HasCompactSupport.intro (isCompact_integralFiniteAdeles F) fun x hx => ?_
    exact Set.indicator_of_notMem (fun h => hx h.2) _
  obtain ⟨d, hd, s, c, hh⟩ := exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs
  refine ⟨d, hd, fun z hz => ?_⟩

  have key : ∀ k : F, (coset d k).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) (ιF F (d : F) * z)
      = (coset d k).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) 0 := by
    intro k
    by_cases h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ coset d k
    · have h1 : ιF F (d : F) * z ∈ coset d k := by
        have := add_mul_mem_coset hd h0 hz
        rwa [zero_add] at this
      rw [Set.indicator_of_mem h0, Set.indicator_of_mem h1, Pi.one_apply, Pi.one_apply]
    · have h1 : ιF F (d : F) * z ∉ coset d k := by
        intro h1
        apply h0
        have := add_mul_mem_coset hd h1 (neg_mem_integral hz)
        rwa [mul_neg, add_neg_cancel] at this
      rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]
  have hval : S.indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) (ιF F (d : F) * z)
      = S.indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ) 0 := by
    rw [hh, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply]
    rw [show ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
        = coset d k from rfl, key k]
  have h0S : (0 : FiniteAdeleRing (𝓞 F) F) ∈ S := ⟨H₁.zero_mem, zero_mem_integral⟩
  rw [Set.indicator_of_mem h0S, Pi.one_apply] at hval
  by_contra hnot
  have : ιF F (d : F) * z ∉ S := fun h => hnot h.1
  rw [Set.indicator_of_notMem this] at hval
  exact zero_ne_one hval

variable {ι : Type} [Fintype ι]

theorem exists_open_periods {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {h : X → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ W : Set X, IsOpen W ∧ (0 : X) ∈ W ∧ (∀ w ∈ W, -w ∈ W) ∧ ∀ x, ∀ w ∈ W, h (x + w) = h x := by

  have hV : ∀ x : X, ∃ V : Set X, IsOpen V ∧ (0 : X) ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, h (x + a + b) = h x := by
    intro x
    obtain ⟨U, hU, hxU, hconst⟩ := (IsLocallyConstant.iff_exists_open h).1 hlc x
    have hU0 : (fun y => x + y) ⁻¹' U ∈ 𝓝 (0 : X) :=
      (hU.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hxU)
    obtain ⟨V, hVo, hV0, hVV⟩ := exists_open_nhds_zero_add_subset hU0
    refine ⟨V, hVo, hV0, fun a ha b hb => ?_⟩
    have : a + b ∈ (fun y => x + y) ⁻¹' U := hVV (Set.add_mem_add ha hb)
    rw [add_assoc]
    exact hconst _ this
  choose V hVo hV0 hVc using hV

  set K := tsupport h with hK
  have hKc : IsCompact K := hcs
  have hcover : K ⊆ ⋃ x ∈ K, (fun y => x + y) '' V x := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨x, hx, 0, hV0 x, by simp⟩
  have hopen : ∀ x ∈ K, IsOpen ((fun y => x + y) '' V x) := fun x _ =>
    (Homeomorph.addLeft x).isOpenMap _ (hVo x)
  obtain ⟨t, htK, htfin, htcover⟩ := hKc.elim_finite_subcover_image hopen hcover

  set W₀ : Set X := ⋂ x ∈ t, V x with hW₀
  set W : Set X := W₀ ∩ (fun w => -w) ⁻¹' W₀ with hW
  have hW₀o : IsOpen W₀ := htfin.isOpen_biInter fun x _ => hVo x
  have hWo : IsOpen W := hW₀o.inter (hW₀o.preimage continuous_neg)
  have hW₀0 : (0 : X) ∈ W₀ := Set.mem_iInter₂.2 fun x _ => hV0 x
  have hW0 : (0 : X) ∈ W := ⟨hW₀0, by simpa using hW₀0⟩
  have hWsymm : ∀ w ∈ W, -w ∈ W := fun w hw => ⟨hw.2, by simpa using hw.1⟩

  have hper : ∀ x ∈ K, ∀ w ∈ W₀, h (x + w) = h x := by
    intro x hx w hw
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (htcover hx)
    obtain ⟨a, ha, rfl⟩ := hxy
    have hwy : w ∈ V y := Set.mem_iInter₂.1 hw y hy
    rw [hVc y a ha w hwy]
    have := hVc y a ha 0 (hV0 y)
    rw [add_zero] at this
    exact this.symm
  refine ⟨W, hWo, hW0, hWsymm, fun x w hw => ?_⟩
  by_cases hx : x ∈ K
  · exact hper x hx w hw.1
  · by_cases hxw : x + w ∈ K
    · have := hper (x + w) hxw (-w) (by simpa using hw.2)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

theorem exists_periods_pi {h : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ (x w : ι → FiniteAdeleRing (𝓞 F) F),
      (∀ i, ∃ z ∈ integralFiniteAdeles (𝓞 F) F, w i = ιF F (d : F) * z) → h (x + w) = h x := by
  obtain ⟨W, hWo, hW0, -, hWper⟩ := exists_open_periods hlc hcs

  let H : AddSubgroup (ι → FiniteAdeleRing (𝓞 F) F) :=
    { carrier := {w | ∀ x, h (x + w) = h x}
      zero_mem' := fun x => by rw [add_zero]
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        rw [neg_add_cancel_right] at this
        exact this.symm }
  have hWH : W ⊆ H := fun w hw x => hWper x w hw

  have hcoord : ∀ i : ι, ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      Pi.single i (ιF F (d : F) * z) ∈ H := by
    intro i
    let Hi : AddSubgroup (FiniteAdeleRing (𝓞 F) F) :=
      H.comap (AddMonoidHom.single (fun _ : ι => FiniteAdeleRing (𝓞 F) F) i)
    have hHi : (Hi : Set (FiniteAdeleRing (𝓞 F) F)) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
      have hc : Continuous (fun z : FiniteAdeleRing (𝓞 F) F =>
          (Pi.single i z : ι → FiniteAdeleRing (𝓞 F) F)) :=
        continuous_single (A := fun _ : ι => FiniteAdeleRing (𝓞 F) F) i
      have : (fun z : FiniteAdeleRing (𝓞 F) F => (Pi.single i z : ι → FiniteAdeleRing (𝓞 F) F)) ⁻¹' W
          ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
        (hWo.preimage hc).mem_nhds (by simpa using hW0)
      exact Filter.mem_of_superset this fun z hz => hWH hz
    obtain ⟨d, hd, hdz⟩ := exists_mul_integral_subset_of_mem_nhds Hi hHi
    exact ⟨d, hd, fun z hz => hdz z hz⟩
  choose dfun hdfun hmem using hcoord
  refine ⟨∏ i, dfun i, Finset.prod_ne_zero_iff.2 fun i _ => hdfun i, fun x w hw => ?_⟩

  have hwH : w ∈ H := by
    rw [← Finset.univ_sum_single w]
    refine H.sum_mem fun i _ => ?_
    obtain ⟨z, hz, hwi⟩ := hw i
    have hsplit : ιF F ((∏ j, dfun j : 𝓞 F) : F) * z
        = ιF F (dfun i : F) * (ιF F ((∏ j ∈ Finset.univ.erase i, dfun j : 𝓞 F) : F) * z) := by
      rw [← mul_assoc, ← map_mul, ← Finset.mul_prod_erase Finset.univ dfun (Finset.mem_univ i)]
      push_cast
      ring
    rw [hwi, hsplit]
    exact hmem i _ (mul_mem_integral (algebraMap_int_mem_integral _) hz)
  exact hwH x

def box (d : 𝓞 F) (k : ι → F) : Set (ι → FiniteAdeleRing (𝓞 F) F) :=
  Set.pi Set.univ fun i => coset d (k i)

omit [Fintype ι] in
theorem mem_box_iff (d : 𝓞 F) (k : ι → F) (x : ι → FiniteAdeleRing (𝓞 F) F) :
    x ∈ box d k ↔ ∀ i, x i ∈ coset d (k i) := by
  simp [box]

omit [Fintype ι] in
theorem box_eq_of_mem {d : 𝓞 F} (hd : d ≠ 0) {k k' : ι → F} {x : ι → FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ box d k) (hx' : x ∈ box d k') : box d k = box d k' := by
  rw [mem_box_iff] at hx hx'
  unfold box
  congr 1
  funext i
  exact coset_eq_of_mem hd (hx i) (hx' i)

theorem isOpen_box {d : 𝓞 F} (hd : d ≠ 0) (k : ι → F) : IsOpen (box d k) :=
  isOpen_set_pi Set.finite_univ fun i _ => isOpen_coset hd (k i)

omit [Fintype ι] in
theorem algebraMap_mem_box (d : 𝓞 F) (k : ι → F) : (fun i => ιF F (k i)) ∈ box d k :=
  (mem_box_iff d k _).2 fun i => algebraMap_mem_coset d (k i)

omit [Fintype ι] in

theorem sub_mem_of_mem_box {d : 𝓞 F} (hd : d ≠ 0) {k : ι → F} {x y : ι → FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ box d k) (hy : y ∈ box d k) :
    ∀ i, ∃ z ∈ integralFiniteAdeles (𝓞 F) F, (x - y) i = ιF F (d : F) * z := by
  intro i
  rw [mem_box_iff] at hx hy
  have h := (mem_coset_iff_of_mem hd (hy i) (x i)).1 (hx i)
  refine ⟨ιF F ((d : F)⁻¹) * (x i - y i), h, ?_⟩
  rw [Pi.sub_apply, ← mul_assoc, mul_inv_cancel_alg hd, one_mul]

omit [Fintype ι] in

theorem exists_mem_box {d : 𝓞 F} (hd : d ≠ 0) (x : ι → FiniteAdeleRing (𝓞 F) F) :
    ∃ k : ι → F, x ∈ box d k := by
  have h : ∀ i, ∃ k : F, x i ∈ coset d k := by
    intro i
    obtain ⟨k', hk'⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F (ιF F ((d : F)⁻¹) * x i)
    refine ⟨-((d : F) * k'), ?_⟩
    rw [mem_coset_iff hd]
    have : ιF F ((d : F)⁻¹) * (x i - ιF F (-((d : F) * k'))) = ιF F k' + ιF F ((d : F)⁻¹) * x i := by
      rw [map_neg, map_mul, sub_neg_eq_add, mul_add, ← mul_assoc, inv_mul_cancel_alg hd, one_mul,
        add_comm]
    rw [this]; exact hk'
  choose k hk using h
  exact ⟨k, (mem_box_iff d k x).2 hk⟩

theorem main {h : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ),
      h = ∑ k ∈ s, c k • (box d k).indicator 1 := by
  obtain ⟨d, hd, hper⟩ := exists_periods_pi hlc hcs

  set K := tsupport h with hK
  have hKc : IsCompact K := hcs
  choose kx hkx using fun x : ι → FiniteAdeleRing (𝓞 F) F => exists_mem_box hd x
  have hcover : K ⊆ ⋃ x ∈ K, box d (kx x) := fun x hx => Set.mem_iUnion₂.2 ⟨x, hx, hkx x⟩
  obtain ⟨t, htK, htfin, htcover⟩ :=
    hKc.elim_finite_subcover_image (fun x _ => isOpen_box hd (kx x)) hcover

  let boxes : Finset (Set (ι → FiniteAdeleRing (𝓞 F) F)) := htfin.toFinset.image fun x => box d (kx x)
  have hrep : ∀ b ∈ boxes, ∃ k : ι → F, box d k = b := by
    intro b hb
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨kx x, rfl⟩
  choose! rep hrep using hrep
  let s : Finset (ι → F) := boxes.image rep
  refine ⟨d, hd, s, fun k => h (fun i => ιF F (k i)), ?_⟩
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]

  have hinj : ∀ k ∈ s, ∀ k' ∈ s, box d k = box d k' → k = k' := by
    intro k hk k' hk' hkk
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hk'
    have : b = b' := by rw [← hrep b hb, ← hrep b' hb', hkk]
    subst this
    rfl
  by_cases hx : ∃ k ∈ s, x ∈ box d k
  · obtain ⟨k, hk, hxk⟩ := hx
    rw [Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem hxk, Pi.one_apply, mul_one]

      obtain hz := sub_mem_of_mem_box hd hxk (algebraMap_mem_box d k)
      have := hper (fun i => ιF F (k i)) (x - fun i => ιF F (k i)) hz
      rw [add_sub_cancel] at this
      exact this
    · intro k' hk' hne
      have hxk' : x ∉ box d k' := fun hxk' => hne (hinj k' hk' k hk (box_eq_of_mem hd hxk' hxk))
      rw [Set.indicator_of_notMem hxk', mul_zero]
    · intro hk'; exact absurd hk hk'
  ·
    push Not at hx
    have hx0 : x ∉ K := by
      intro hxK
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (htcover hxK)
      have hb : box d (kx y) ∈ boxes := Finset.mem_image.2 ⟨y, htfin.mem_toFinset.2 hy, rfl⟩
      have hks : rep (box d (kx y)) ∈ s := Finset.mem_image.2 ⟨_, hb, rfl⟩
      apply hx _ hks
      rw [hrep _ hb]
      exact hxy
    rw [image_eq_zero_of_notMem_tsupport hx0]
    symm
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Set.indicator_of_notMem (hx k hk), mul_zero]

end NumberField.AdelicBox.PiDecomposition

end

open _root_.NumberField _root_.P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles.NumberField _root_.NumberField.AdelicBox _root_.P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles.NumberField.AdelicBox NumberField.AdelicBox.PiDecomposition IsDedekindDomain in

theorem solution
    (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    {h : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ),
      h = ∑ k ∈ s, c k •
        (Set.pi Set.univ fun i => (fun z : FiniteAdeleRing (𝓞 F) F ↦
            algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i)
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 :=
  main hlc hcs

end S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles
end P2MW
export P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles (solution)
