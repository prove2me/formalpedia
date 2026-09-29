-- Prove2me | solution 1 for ModularCurve.eisensteinQuotientRationalLocalized_qPowQuotient_le_h1Jtors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/fb149918-9505-5189-8335-83e93ad90fad

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinQuotientRationalLocalized_qPowQuotient_le_h1Jtors

set_option autoImplicit false

open ModularCurve AlgebraicCurve

section RA

variable {A : Type*} [AddCommGroup A]

private theorem index_range_eq_of_map_le (f : A →+ A) (N : AddSubgroup A) [N.FiniteIndex]
    (hmap : N.map f ≤ N) :
    f.range.index = (N.map f).relIndex N * N.relIndex f.ker := by
  have h1 : (N.map f).index = (N ⊔ f.ker).index * f.range.index := N.index_map f
  have h2 : (N.map f).relIndex N * N.index = (N.map f).index :=
    AddSubgroup.relIndex_mul_index hmap
  have h3 : N.relIndex (N ⊔ f.ker) * (N ⊔ f.ker).index = N.index :=
    AddSubgroup.relIndex_mul_index le_sup_left
  have hsup0 : (N ⊔ f.ker).index ≠ 0 := by
    intro h0
    have hdvd : (N ⊔ f.ker).index ∣ N.index := AddSubgroup.index_dvd_of_le le_sup_left
    rw [h0] at hdvd
    exact AddSubgroup.FiniteIndex.index_ne_zero (H := N) (Nat.eq_zero_of_zero_dvd hdvd)
  have hsupl : N.relIndex (N ⊔ f.ker) = N.relIndex f.ker :=
    AddSubgroup.relIndex_sup_left f.ker N
  have hcomb : ((N.map f).relIndex N * N.relIndex f.ker) * (N ⊔ f.ker).index
      = f.range.index * (N ⊔ f.ker).index := by
    calc ((N.map f).relIndex N * N.relIndex f.ker) * (N ⊔ f.ker).index
        = (N.map f).relIndex N * (N.relIndex (N ⊔ f.ker) * (N ⊔ f.ker).index) := by
          rw [hsupl, mul_assoc]
      _ = (N.map f).relIndex N * N.index := by rw [h3]
      _ = (N.map f).index := h2
      _ = (N ⊔ f.ker).index * f.range.index := h1
      _ = f.range.index * (N ⊔ f.ker).index := mul_comm _ _
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hsup0) hcomb).symm

private theorem relIndex_le_card (N K : AddSubgroup A) [Finite ↥K] :
    N.relIndex K ≤ Nat.card ↥K := by
  show (N.addSubgroupOf K).index ≤ Nat.card ↥K
  rw [AddSubgroup.index_eq_card]
  exact Nat.card_le_card_of_surjective _ QuotientAddGroup.mk_surjective

private theorem index_range_le_of_map_le (f : A →+ A) (N : AddSubgroup A) [N.FiniteIndex]
    (hmap : N.map f ≤ N) (hker : Finite ↥f.ker) :
    f.range.index ≤ (N.map f).relIndex N * Nat.card ↥f.ker := by
  haveI := hker
  rw [index_range_eq_of_map_le f N hmap]
  exact Nat.mul_le_mul_left _ (relIndex_le_card N f.ker)

end RA

private theorem finite_torsion_of_fg (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    Finite ↥(AddCommGroup.torsion A) := by
  haveI : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr ‹AddGroup.FG A›
  haveI : AddGroup.FG ↥(AddCommGroup.torsion A) := by
    rw [AddGroup.fg_iff_addSubgroup_fg,
      ← AddSubgroup.toIntSubmodule_toAddSubgroup (AddCommGroup.torsion A),
      ← Submodule.fg_iff_addSubgroup_fg]
    exact IsNoetherian.noetherian _
  refine AddCommGroup.finite_of_fg_torsion _ fun ⟨x, hx⟩ => ?_
  obtain ⟨n, npos, hn⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, npos, Subtype.ext (by simpa using hn)⟩

private theorem relIndex_map_range_eq_index {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (i : B →+ A) (hi : Function.Injective i) (f : A →+ A) (g : B →+ B)
    (hfg : f.comp i = i.comp g) :
    (i.range.map f).relIndex i.range = g.range.index := by
  have h1 : i.range.map f = g.range.map i := by
    rw [AddMonoidHom.range_eq_map i, AddMonoidHom.range_eq_map g, AddSubgroup.map_map,
      AddSubgroup.map_map, hfg]
  rw [h1, AddMonoidHom.range_eq_map i, AddSubgroup.relIndex_map_map_of_injective _ _ hi,
    AddSubgroup.relIndex_top_right]

private theorem index_le_card_of_ker_eq {B H : Type*} [AddCommGroup B] [AddCommGroup H]
    [Finite H] (δ : B →+ H) (S : AddSubgroup B) (hker : δ.ker = S) :
    S.index ≤ Nat.card H := by
  rw [← hker, AddSubgroup.index_ker]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

private theorem ker_zsmul_id_le_torsion {A : Type*} [AddCommGroup A] {k : ℤ} (hk : k ≠ 0) :
    (k • AddMonoidHom.id A).ker ≤ AddCommGroup.torsion A := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨k, hk, hx⟩

private theorem index_range_zsmul_le {A B H : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup H] [Finite H] [Finite ↥(AddCommGroup.torsion A)]
    (i : B →+ A) (hi : Function.Injective i) [i.range.FiniteIndex]
    (δ : B →+ H) {k : ℤ} (hk : k ≠ 0)
    (hker : δ.ker = ((k • (AddMonoidHom.id B : B →+ B)).range : AddSubgroup B)) :
    ((k • (AddMonoidHom.id A : A →+ A)).range : AddSubgroup A).index
      ≤ Nat.card ↥(AddCommGroup.torsion A) * Nat.card H := by
  have hle : (k • (AddMonoidHom.id A : A →+ A)).ker ≤ AddCommGroup.torsion A :=
    ker_zsmul_id_le_torsion hk
  haveI : Finite ↥(k • (AddMonoidHom.id A : A →+ A)).ker :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective hle)
  have hmap : i.range.map (k • (AddMonoidHom.id A : A →+ A)) ≤ i.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact i.range.zsmul_mem hx k
  have hfg : (k • (AddMonoidHom.id A : A →+ A)).comp i
      = i.comp (k • (AddMonoidHom.id B : B →+ B)) := by
    ext x
    exact (map_zsmul i k x).symm
  calc ((k • (AddMonoidHom.id A : A →+ A)).range : AddSubgroup A).index
      ≤ (i.range.map (k • (AddMonoidHom.id A : A →+ A))).relIndex i.range
          * Nat.card ↥(k • (AddMonoidHom.id A : A →+ A)).ker :=
        index_range_le_of_map_le _ _ hmap inferInstance
    _ = ((k • (AddMonoidHom.id B : B →+ B)).range : AddSubgroup B).index
          * Nat.card ↥(k • (AddMonoidHom.id A : A →+ A)).ker := by
        rw [relIndex_map_range_eq_index i hi _ _ hfg]
    _ ≤ Nat.card H * Nat.card ↥(AddCommGroup.torsion A) :=
        Nat.mul_le_mul (index_le_card_of_ker_eq δ _ hker) (AddSubgroup.card_le_of_le hle)
    _ = Nat.card ↥(AddCommGroup.torsion A) * Nat.card H := Nat.mul_comm _ _

private theorem smul_mem_rational (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ (t : HeckeAlg), ∀ z ∈ eisensteinQuotientRational p (heckeModuleBar p),
      t • z ∈ eisensteinQuotientRational p (heckeModuleBar p) := by
  letI := heckeModuleBar p
  haveI := smulCommClass_JZero_of_heckeOperatorsCommuteBar p hcomm
  rintro t z ⟨x, hx, rfl⟩
  refine ⟨t • x, ?_, ?_⟩
  · intro σ
    have h := (eisensteinKernelSubmodule p (heckeModuleBar p)).smul_mem t (hx σ)
    rwa [smul_sub, ← smul_comm σ t x] at h
  · rfl

private theorem smul_mem_closure_rational (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ (t : HeckeAlg), ∀ w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)),
      t • w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)) := by
  letI := heckeModuleBar p
  intro t w hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure (smul_mem_rational p hcomm t x hx)
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

private theorem span_le_closure (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ w ∈ Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)),
      w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)) := by
  letI := heckeModuleBar p
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact AddSubgroup.subset_closure hx
  | zero => exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => exact AddSubgroup.add_mem _ hx hy
  | smul t x _ hx => exact smul_mem_closure_rational p hcomm t x hx

private theorem addGroup_fg_of_le {A : Type*} [AddCommGroup A] {H K : AddSubgroup A}
    (hHK : H ≤ K) (hK : AddGroup.FG ↥K) : AddGroup.FG ↥H := by
  haveI : Module.Finite ℤ ↥K := Module.Finite.iff_addGroup_fg.mpr hK
  haveI : AddGroup.FG ↥(H.addSubgroupOf K) := by
    rw [AddGroup.fg_iff_addSubgroup_fg, ← AddSubgroup.toIntSubmodule_toAddSubgroup (H.addSubgroupOf K),
      ← Submodule.fg_iff_addSubgroup_fg]
    exact IsNoetherian.noetherian _
  exact AddGroup.fg_of_surjective (f := (AddSubgroup.addSubgroupOfEquivOfLe hHK).toAddMonoidHom)
    (AddSubgroup.addSubgroupOfEquivOfLe hHK).surjective

section RL

variable {S : Type*} [CommRing S]

private def finOrderSubmodule (N : Type*) [AddCommGroup N] [Module S N] : Submodule S N where
  carrier := {x | IsOfFinAddOrder x}
  add_mem' {a b} ha hb := (AddCommGroup.torsion N).add_mem ha hb
  zero_mem' := (AddCommGroup.torsion N).zero_mem
  smul_mem' r x hx := by
    obtain ⟨n, hn0, hn⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).mp hx
    exact (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨n, hn0, by rw [smul_comm, hn, smul_zero]⟩

private theorem finite_torsion_localizedModule (W : Submonoid S) (N : Type*) [AddCommGroup N]
    [Module S N] [AddGroup.FG N] :
    Finite ↥(AddCommGroup.torsion (LocalizedModule W N)) := by
  haveI hT : Finite ↥(finOrderSubmodule (S := S) N) := finite_torsion_of_fg N

  have hsurj : ∀ (t : ↥(finOrderSubmodule (S := S) N)) (s : W),
      ∃ t' : ↥(finOrderSubmodule (S := S) N),
        (LocalizedModule.mk (t : N) s : LocalizedModule W N) = LocalizedModule.mk (t' : N) 1 := by
    intro t s
    obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun i : ℕ => fun x : ↥(finOrderSubmodule (S := S) N) => ((s : S) ^ i • x))

    have key : ∀ {a b : ℕ}, a < b →
        (fun x : ↥(finOrderSubmodule (S := S) N) => ((s : S) ^ a • x)) =
          (fun x => ((s : S) ^ b • x)) →
        ∃ t' : ↥(finOrderSubmodule (S := S) N),
          (LocalizedModule.mk (t : N) s : LocalizedModule W N) = LocalizedModule.mk (t' : N) 1 := by
      intro a b hlt hfun
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      refine ⟨(s : S) ^ d • t, ?_⟩
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨(s : S) ^ a, pow_mem s.2 a⟩, ?_⟩
      have h1 := congrArg Subtype.val (congrFun hfun t)
      simp only [Submodule.coe_smul] at h1
      simp only [one_smul, Submonoid.smul_def, Submodule.coe_smul, smul_smul]
      rw [h1]
      congr 1
      ring
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key h heq
    · exact key h heq.symm

  have hrange : ∀ y : LocalizedModule W N, IsOfFinAddOrder y →
      y ∈ Set.range (fun t : ↥(finOrderSubmodule (S := S) N) =>
        (LocalizedModule.mk (t : N) 1 : LocalizedModule W N)) := by
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨k, hk0, hk⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).mp hy
      have h1 : (k • LocalizedModule.mk n s : LocalizedModule W N) = LocalizedModule.mk (k • n) s := by
        rw [← Nat.cast_smul_eq_nsmul S, LocalizedModule.smul'_mk, Nat.cast_smul_eq_nsmul]
      rw [h1, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hk
      obtain ⟨u, hu⟩ := hk
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, smul_smul, smul_comm] at hu

      have hmem : ((u : S) * (s : S)) • n ∈ finOrderSubmodule (S := S) N :=
        (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨k, hk0, hu⟩
      obtain ⟨t', ht'⟩ := hsurj ⟨_, hmem⟩ (u * s * s)
      refine ⟨t', ?_⟩
      show LocalizedModule.mk (t' : N) 1 = LocalizedModule.mk n s
      rw [← ht', LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def, smul_smul]
      congr 1
      push_cast
      ring
  have hsub : ((AddCommGroup.torsion (LocalizedModule W N) : Set (LocalizedModule W N))) ⊆
      Set.range (fun t : ↥(finOrderSubmodule (S := S) N) =>
        (LocalizedModule.mk (t : N) 1 : LocalizedModule W N)) := fun y hy => hrange y hy
  exact ((Set.finite_range _).subset hsub).to_subtype

end RL

set_option maxHeartbeats 3200000 in

theorem solution (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime]
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (R : ∀ m : ℕ, JKummerRow q m (eisensteinQuotientRationalLocalized p q))
    (hfinH : ∀ m : ℕ, letI := (R m).instH1Jtors; Finite (R m).H1Jtors) :
    ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ m : ℕ,
      letI := (R m).instH1Jtors
      (@AddMonoidHom.range (eisensteinQuotientRationalLocalized p q) _
          (eisensteinQuotientRationalLocalized p q) _
          ((q : ℤ) ^ m • AddMonoidHom.id (eisensteinQuotientRationalLocalized p q))).index ≤ c₀ * Nat.card (R m).H1Jtors := by

  letI := heckeModuleBar p
  have hq : q.Prime := Fact.out
  haveI hfgspan : AddGroup.FG
      ↥(Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) :=
    addGroup_fg_of_le
      (H := (Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))).toAddSubgroup)
      (fun w hw => span_le_closure p hcomm w hw) hfgc
  haveI : Finite ↥(AddCommGroup.torsion (eisensteinQuotientRationalLocalized p q)) :=
    finite_torsion_localizedModule (S := HeckeAlg) (eisensteinMaximalIdeal p q).primeCompl
      ↥(Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)))
  refine ⟨Nat.card ↥(AddCommGroup.torsion (eisensteinQuotientRationalLocalized p q)),
    Nat.card_pos, fun m => ?_⟩
  letI := (R m).instM0
  letI := (R m).instH1Jtors
  haveI := hfinH m
  haveI := (R m).toM_finiteIndex
  have hk : ((q : ℤ) ^ m) ≠ 0 := pow_ne_zero m (by exact_mod_cast hq.ne_zero)
  have hmain := index_range_zsmul_le (R m).toM (R m).toM_injective (R m).delta hk (R m).delta_ker
  convert hmain using 3 <;> try rfl
  ext x
  simp

end S_ModularCurve_eisensteinQuotientRationalLocalized_qPowQuotient_le_h1Jtors
end P2MW
export P2MW.S_ModularCurve_eisensteinQuotientRationalLocalized_qPowQuotient_le_h1Jtors (solution)
