-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:15:03.634982+00:00
-- url     : https://prove2.me/submissions/f6692801-f00e-4cce-b0e3-8f76f9d9ab20

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_vtx
import Theorems.Thm_KnodelPrimeCordial_cyclic_model
import Theorems.Thm_KnodelPrimeCordial_primeCordial_transport__p2m_b71a112c_d89d_4dc4_9a88_bb82c5bac86c_a1

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n)
    (f : Fin n → ℕ)
    (hf : KnodelPrimeCordial.IsPrimeCordialLabeling (KnodelPrimeCordial.cyc n) f) :
    ∃ g : Fin 2 × Fin (n / 2) → ℕ,
      KnodelPrimeCordial.IsPrimeCordialLabeling (KnodelPrimeCordial.knodel 3 n) g := by
  have hmodel := KnodelPrimeCordial.cyclic_model n hn (by omega)
  let e : Fin n ≃ Fin 2 × Fin (n / 2) :=
    Equiv.ofBijective (KnodelPrimeCordial.vtx n (by omega)) hmodel.1
  exact KnodelPrimeCordial.primeCordial_transport__p2m_b71a112c_d89d_4dc4_9a88_bb82c5bac86c_a1
    (G := KnodelPrimeCordial.cyc n) (H := KnodelPrimeCordial.knodel 3 n)
    e hmodel.2 f hf
